package maf.modular.scheme.modflocal

import maf.language.scheme._
import maf.modular.scheme._
import maf.modular.worklist._
import maf.util.benchmarks.Timeout
import maf.modular.AddrDependency

trait SchemeModFLocalAdaptiveWidening(k: Int, c: Double = 0.5) extends SchemeModFLocal with SequentialWorklistAlgorithm[SchemeExp]:
    this: SchemeModFLocalSensitivity with SchemeDomain =>

    def debug(msg: => String) = ()

    // THE WIDENED SET DETERMINES WHICH ADDRESSES ARE WIDENED

    var widened: Set[Adr] = Set.empty
    override def customPolicy(adr: Adr): AddrPolicy =
      if widened(adr) then AddrPolicy.Widened else AddrPolicy.Local

    // BOOKKEEPING: keep track of all components per (lam, ctx)
    var cmps: Map[(Lam, Ctx), Set[Cll]] = Map.empty
    def ratio: Double = (visited.size - 1) / Math.max(1, cmps.size)

    // THE SHADOW STORE (& DEPS)
    var shadowStore: Map[Adr, Val] = Map.empty
    var shadowDeps: Map[Adr, Set[Cmp]] = Map.empty

    override def step(t: Timeout.T) =
        super.step(t)
        if ratio > k then
            val oldRatio = ratio
            debug("ADAPTING")
            adaptAnalysis()
            debug(s"--> ${widened.size} addresses have been widened in total.")
            val newRatio = ratio
            debug(s"Ratio: $oldRatio -> $newRatio")

    override def spawn(cmp: Cmp) =
        if (!visited(cmp)) then
            val cll @ CallComponent(lam, _, ctx, sto) = cmp
            cmps += (lam, ctx) -> (cmps.getOrElse((lam, ctx), Set.empty) + cll)
        super.spawn(cmp)

    private def adaptAnalysis() =
        val max = cmps.maxBy((_, cls) => cls.size)._2.size
        val cut = Math.max(1, max * c).toInt
        val sel = cmps.filter((_, cls) => cls.size >= cut)
        val wid = sel.flatMap((_, cls) => pickAddrs(cls.map(_.sto), cut)).toSet
        addWidened(wid)

    private def pickAddrs(sts: Set[Sto], cut: Int): Set[Adr] =
        val ads = sts.foldLeft(Map.empty[Adr, Set[(Val, Cnt)]]) { (acc, sto) =>
          sto.content.foldLeft(acc) { case (acc2, (adr, bnd)) =>
            acc2.get(adr) match
                case None      => acc2 + (adr -> Set(bnd))
                case Some(bds) => acc2 + (adr -> (bds + bnd))
          }
        }
        val lst = ads.toList.sortBy((_, bds) => bds.size)(Ordering[Int].reverse).map(_._1)
        pickAddrsRec(lst, sts, cut)

    private def pickAddrsRec(lst: List[Adr], sts: Set[Sto], cut: Int): Set[Adr] =
      if sts.size > cut then
          val adr :: rst = lst
          pickAddrsRec(rst, sts.map(_ - adr), cut) + adr
      else Set.empty

    // NOTE/TODO: not safe for parallelisation
    override protected def lookupLocalV(cmp: Cmp, sto: Sto, adr: Adr): Option[Val] = 
        shadowDeps += adr -> (shadowDeps.getOrElse(adr, Set.empty) + cmp)
        super.lookupLocalV(cmp, sto, adr) 

    override protected def extendLocalV(cmp: Cmp, sto: Sto, adr: Adr, vlu: Val): Dlt =
        updateAddr(shadowStore, adr, vlu).foreach(upd => shadowStore = upd)
        super.extendLocalV(cmp, sto, adr, vlu)

    override protected def updateLocalV(cmp: Cmp, sto: Sto, adr: Adr, vlu: Val): Dlt =
        updateAddr(shadowStore, adr, vlu).foreach(upd => shadowStore = upd)
        super.updateLocalV(cmp, sto, adr, vlu)      

    private def addWidened(wid: Set[Adr]) =
        // helper functions
        def widenSto(sto: Sto): Sto = sto -- wid
        def widenDlt(dlt: Dlt): Dlt = dlt -- wid
        def widenCll(cll: Cll): Cll = cll.copy(sto = widenSto(cll.sto))
        def widenCmp(cmp: Cmp): Cmp =
          cmp match
              case MainComponent => cmp
              case cll: Cll      => widenCll(cll)
        def widenDep(dep: Dep): Dep =
          dep match
              case res: ResultDependency => res.copy(cmp = widenCmp(res.cmp))
              case _                     => dep
        // add widened addresses
        widened ++= wid
        // update analysis data
        visited = visited.map(widenCmp)
        workList = workList.map(widenCmp)
        deps = deps
          .foldLeft(Map.empty[Dep, Set[Cmp]]) { case (acc, (dep, cps)) =>
            val updatedCps = cps.map(widenCmp)
            val updatedDep = widenDep(dep)
            acc.get(updatedDep) match
                case None      => acc + (updatedDep -> updatedCps)
                case Some(oth) => acc + (updatedDep -> (oth ++ updatedCps))
          }
          .withDefaultValue(Set.empty)
        cmps = cmps.map((nod, cls) => (nod, cls.map(widenCll)))
        shadowDeps = shadowDeps.map((dep, cps) => (dep, cps.map(widenCmp)))
        // widen addresses (using shadow store & deps)
        widened.foreach { adr =>
          writeAddr(adr, shadowStore.getOrElse(adr, lattice.bottom))
          val cps = shadowDeps.getOrElse(adr, Set.empty)
          deps += AddrDependency(adr) -> cps
          addToWorkList(cps)
          shadowStore -= adr
          shadowDeps -= adr
        }
        // update results
        var merged: Set[Cmp] = Set.empty
        results = results.foldLeft(Map.empty: Res) { case (acc, (cmp, (vlu, dlt))) =>
          val updatedCmp = widenCmp(cmp)
          val updatedDlt = widenDlt(dlt)
          acc.get(updatedCmp) match
              case None =>
                acc + (updatedCmp -> (vlu, updatedDlt))
              case Some((othVlu, othDlt)) =>
                merged += updatedCmp
                acc + (updatedCmp -> (lattice.join(othVlu, vlu), updatedCmp.sto.join(othDlt, updatedDlt)))
        }
        merged.foreach(cmp => trigger(ResultDependency(cmp)))
      