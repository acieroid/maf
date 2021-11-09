package maf.aam.scheme

import maf.aam.{AAMAnalysis, GraphElementAAM}

import maf.util.*
import maf.modular.scheme._
import maf.core.Position._
import maf.core._
import maf.language.scheme._
import maf.language.scheme.primitives._
import maf.util.benchmarks.Timeout
import maf.language.sexp
import maf.language.CScheme._
import maf.lattice.interfaces.BoolLattice
import maf.lattice.interfaces.LatticeWithAddrs
import maf.util.graph.{Graph, GraphElement}
import maf.util.graph.Colors

/** An AAM style semantics for Scheme */
abstract class SchemeAAMSemantics(prog: SchemeExp) extends AAMAnalysis with SchemeDomain:
    type Val
    type LatVal = Value
    type Expr = SchemeExp
    type Kont = Frame
    type Sto = BasicStore[Address, Storable]
    type Lam = SchemeLambdaExp
    type State = SchemeState
    type Env = Environment[Address]
    type Ctx = Unit // TODO: fix
    type Ext

    override def analyzeWithTimeout[G](timeout: Timeout.T, graph: G)(using Graph[G, GraphElementAAM, GraphElement]): (Set[State], G) =
      analyze(prog, graph, timeout)

    /** An instantation of the <code>SchemeInterpreterBridge</code> trait to support the builtin MAF Scheme primitives */
    private class InterpreterBridge(env: Env, private var sto: Sto, kont: Address, t: Timestamp) extends SchemeInterpreterBridge[LatVal, Address]:
        def pointer(exp: SchemeExp): Address =
          alloc(exp.idn, env, sto, kont, t)

        def callcc(clo: Closure, pos: Position): LatVal = throw new Exception("not supported")
        def readSto(a: Address): LatVal =
            import Storable.*
            sto
              .lookup(a)
              .map {
                case V(v) => v
                case _    => lattice.bottom
              }
              .getOrElse(lattice.bottom)

        def writeSto(a: Address, value: LatVal): Unit =
          sto = sto.extend(a, Storable.V(value))

        def currentThread: TID =
          throw new Exception("unsupported")

        def updatedSto: Sto =
          sto

    /**
     * The `Storable` enum represents values that can be stored in the store. To enable approximating semantics we define a lattice over these
     * storable values below.
     */
    enum Storable:
        /** We can store values in the store */
        case V(v: LatVal)

        /** We can also store continuations in the store */
        case K(k: Set[Kont])

    /** Inject the values from the lattice's abstract domain in the (possibly extended) domain of a sub analysis */
    def inject(v: LatVal): Val

    /** Project the (possibly extended) domain of a sub analysis to the lattice domain */
    def project(v: Val): LatVal

    /** Instantiation of the `Storable` lattice. Only elements of the same type can be joined together, and there are no bottom or top elements */
    given storableLattice: Lattice[Storable] with
        import Storable.*
        def bottom: Storable =
          Storable.V(lattice.bottom)

        def top: Storable = throw new Exception("storables have no single top element")
        def join(x: Storable, y: => Storable): Storable = (x, y) match
            case (V(v1), V(v2)) =>
              V(lattice.join(v1, v2))
            case (K(k1), K(k2)) =>
              K(k1 ++ k2)
            case _ =>
              throw new Exception(s"joining elements $x and $y not supported in storable lattice")

        def subsumes(x: Storable, y: => Storable): Boolean = throw new Exception("NYI")
        def eql[B: BoolLattice](x: Storable, y: Storable): B = throw new Exception("NYI")
        def show(v: Storable): String = v match
            case V(v1) => s"V($v1)"
            case K(k1) => s"K($k1)"

    /**
     * An address under which a continuation is stored. To preserve call-return semantics, this address should be (e, p) where e is the call targets
     * control and environment respectively (Gilray et al., 2016).
     */
    case class KontAddr(expr: SchemeExp, env: Env, timestamp: Timestamp) extends Address:
        def idn: Identity = expr.idn
        def printable = true
        override def toString = s"KontAddr(${expr} ${timestamp})"

    case class RetAddr(expr: SchemeExp, timestamp: Timestamp) extends Address:
        def idn: Identity = Identity.none
        def printable = true
        override def toString = s"RetAddr(${expr} ${timestamp})"

    /** The location of the initial continuaton */
    case object Kont0Addr extends Address:
        def idn: Identity = Identity.none
        def printable = true
        override def toString = s"Kont0Addr"

    /** An address on which values will be allocated */
    case class ValAddr(lam: Lam, ctx: Ctx) extends Address:
        def idn: Identity = lam.idn
        def printable = true
        override def toString = s"ValAddr(${lam}, ${ctx})"

    /** The address at which the values of function parameters are allocated */
    case class VarAddr(ide: Identity, ctx: Ctx) extends Address:
        def idn: Identity = ide
        def printable = true
        override def toString = s"VarAddr(${ide}, ${ctx})"

    /** An address on which location a primitive can be stored */
    case class PrimAddr(name: String) extends Address:
        def idn: Identity = Identity.none
        def printable = true
        override def toString = s"PrimAddr($name)"

    /** Read from the given address in the store, returns V(bottom) if no value is found at the given address. */
    def readSto(sto: Sto, addr: Address): Storable =
      sto.lookup(addr).getOrElse(Storable.V(lattice.bottom))

    def readStoV(sto: Sto, addr: Address): Val =
      sto
        .lookup(addr)
        .collectFirst { case Storable.V(v) =>
          inject(v)
        }
        .getOrElse(inject(lattice.bottom))

    /** Write to the given address in the store, returns the updated store */
    def writeSto(sto: Sto, addr: Address, value: Storable): Sto =
      sto.extend(addr, value)

    /** Write a value to the given address in the store, returns the updated store */
    def writeStoV(sto: Sto, addr: Address, value: Val): Sto =
      writeSto(sto, addr, Storable.V(project(value)))

    private def preprocessProgram(program: List[SchemeExp]): SchemeExp =
        val originalProgram = program
        val preludedProgram = SchemePrelude.addPrelude(originalProgram)
        CSchemeUndefiner.undefine(preludedProgram)

    lazy val initialBds: Iterable[(String, Address, Storable)] =
      primitives.allPrimitives.view
        .map { case (name, p) =>
          (name, PrmAddr(name), Storable.V(lattice.primitive(p.name)))
        }

    sealed trait Frame:
        def link(next: Address): Frame
    case class AssFrame(id: Identifier, env: Env, next: Option[Address] = None) extends Frame:
        def link(next: Address): AssFrame =
          AssFrame(id, env, Some(next))
    case class BegFrame(exps: List[Expr], env: Env, next: Option[Address] = None) extends Frame:
        def link(next: Address): BegFrame =
          this.copy(next = Some(next))
    case class IteFrame(csq: Expr, alt: Expr, env: Env, next: Option[Address] = None) extends Frame:
        def link(next: Address): IteFrame =
          this.copy(next = Some(next))
    case class LetFrame(
        // evaluated bindings
        evalBds: List[(Identifier, Val)],
        // the bindings that still need to be evaluated
        bindings: List[(Identifier, SchemeExp)],
        // the body of the let
        body: List[SchemeExp],
        env: Env,
        next: Option[Address] = None)
        extends Frame:

        def link(next: Address): LetFrame =
          this.copy(next = Some(next))

    case class LetStarFrame(
        currentIdentifier: Identifier,
        bindings: List[(Identifier, SchemeExp)],
        body: List[SchemeExp],
        env: Env,
        next: Option[Address] = None)
        extends Frame:
        def link(next: Address): LetStarFrame =
          this.copy(next = Some(next))

    case class LetrecFrame(
        addresses: List[Address],
        valeus: List[Val],
        bindings: List[(Identifier, SchemeExp)],
        body: List[SchemeExp],
        env: Env,
        next: Option[Address] = None)
        extends Frame:
        def link(next: Address): LetrecFrame =
          this.copy(next = Some(next))

    case object HltFrame extends Frame:
        def link(next: Address): Frame = this

    /**
     * A continuation for evaluating a function.
     *
     * @param f
     *   the original Scheme expression corresponding to the function call
     * @param args
     *   the list of arguments that still need to be evaluated
     */
    case class FunFrame(f: SchemeFuncall, args: List[SchemeExp], env: Env, next: Option[Address] = None) extends Frame:
        def link(next: Address): FunFrame =
          this.copy(next = Some(next))

    case class ArgFrame(
        f: SchemeFuncall,
        args: List[SchemeExp],
        fv: Val,
        argV: List[Val],
        env: Env,
        next: Option[Address] = None)
        extends Frame:
        def link(next: Address): ArgFrame =
          this.copy(next = Some(next))

    /** The control of the CESK* machine */
    enum Control:
        /** Instruction to evaluate the given expression */
        case Ev(expr: Expr, env: Env)

        /** Instruction to apply the continuation that is on top of the continuation stack */
        case Ap(value: Val)

    /** Provide a default "empty" extension to the state of the AAM-based analysis */
    protected def emptyExt: Ext

    /** A state of the Scheme AAM machine */
    case class SchemeState(c: Control, s: Sto, k: Address, t: Timestamp, extra: Ext):
        override def toString: String =
            val control = c match {
              case Control.Ev(expr, env) => s"ev(${expr.toString})"
              case Control.Ap(vlu)       => s"ap(${vlu.toString})"
            }

            s"($control, ${s.content.size}, $k)"

    /** Inject the initial state for the given expression */
    def inject(expr: Expr): State =
        val initialEnv = BasicEnvironment(initialBds.map(p => (p._1, p._2)).toMap)
        val initialStore = BasicStore(initialBds.map(p => (p._2, p._3)).toMap).extend(Kont0Addr, Storable.K(Set(HltFrame)))
        SchemeState(Control.Ev(expr, initialEnv), initialStore, Kont0Addr, initialTime, emptyExt)

    /** Returns a string representation of the store. */
    def storeString(store: Sto, primitives: Boolean = false): String =
        val strings = store.content.map({ case (a, v) => s"${StringUtil.toWidth(a.toString, 50)}: $v" })
        val filtered = if primitives then strings else strings.filterNot(_.toLowerCase.nn.startsWith("prm"))
        val size = filtered.size
        val infoString = "σ" * 150 + s"\nThe store contains $size addresses (primitive addresses ${if primitives then "included" else "excluded"}).\n"
        filtered.toList.sorted.mkString(infoString, "\n", "\n" + "σ" * 150)

    /** Print a debug version of the given state */
    def printDebug(s: State, printStore: Boolean = false): Unit =
        println(s)
        if printStore then println(storeString(s.s, false))

    def compareStates(s1: State, s2: State): Boolean =
        println("==================================================================================")
        for (k, v) <- s1.s.content do
            if s2.s.content.contains(k) && v != s2.s.content(k) then println(s"Difference detected at $k of $v and ${s2.s.content(k)}")
        println("==================================================================================")

        true

    def isFinal(st: State): Boolean =
      (st.k == Kont0Addr && (st.c match { case Control.Ap(_) => true; case _ => false }))

    def extractValue(st: State): Option[Val] =
      st.c match
          case Control.Ap(v) => Some(v)
          case _             => None

    /** Convert the given state to a node in a graph */
    def asGraphElement(s: State): GraphElementAAM = s.c match
        case Control.Ev(e, _) => GraphElementAAM(s.hashCode, label = s"ev($e)", color = Colors.Yellow, data = "")
        case Control.Ap(v)    => GraphElementAAM(s.hashCode, label = s"ap($v)", color = Colors.Red, data = "")

    /** Step from one state to another */
    def step(s0: State): Set[State] =
        import Control.*
        s0 match
            case SchemeState(Ev(expr, env), sto, kont, t, ext) => eval(expr, env, sto, kont, t, ext)
            case SchemeState(Ap(value), sto, kont, t, ext)     => continue(value, sto, kont, t, ext)

    /**
     * Push a frame on the conceptual stack of continuation frames
     *
     * @return
     *   a pair of the updated store (since continuations are store allocated), and the address at which the continuation has been allocated
     */
    protected def pushFrame(
        e: Expr,
        env: Env,
        sto: Sto,
        next: Address,
        frame: Kont,
        t: Timestamp
      ): (Sto, Address, Timestamp) =
        val timestamp = tick(t, e, sto, next)
        val addr = KontAddr(e, env, timestamp)
        val sto1 = writeSto(sto, addr, Storable.K(Set(frame.link(next))))
        (sto1, addr, timestamp)

    /** Evaluate the given expression */
    def eval(
        expr: Expr,
        env: Env,
        sto: Sto,
        kont: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] = expr match
        // (Ev(literal), env, sto, kont) ==> (Ap(inj(literal)), env, sto, kont)
        case lit: SchemeValue =>
          evalLiteralVal(lit, env, sto, kont, t, ext)

        // (Ev((lambda (x) e)), env, sto, kont) ==> (Ap(inj(closure(x, e))), env, sto, kont)
        case lam: SchemeLambdaExp =>
          Set(SchemeState(Control.Ap(inject(lattice.closure((lam, env.restrictTo(lam.fv))))), sto, kont, t, ext))

        // (Ev(x), env, sto, kont) ==> (Ap(inj(v)), env, sto, kont)
        //    where: v = sto(env(x))
        case SchemeVar(id) =>
          evalVariable(id, env, sto, kont, t, ext)
        // (Ev((set! x e)), env, sto, kont) ==> (Ev(e), env, sto, assgn(x) :: kont)
        case SchemeSet(id, exp, _) =>
          val (sto1, frame, t1) = pushFrame(exp, env, sto, kont, AssFrame(id, env), t)
          Set(SchemeState(Control.Ev(exp, env), sto1, frame, t1, ext))

        // (Ev((begin e1 e2 ... en)), env, sto, kont) ==> (Ev(e1), env, sto, beg(e2 ... en) :: kont)
        case SchemeBegin(exps, _) =>
          evaluate_sequence(env, sto, kont, exps, t, ext)

        // (Ev((if prd csq alt)), env, sto, kont) ==> (Ev(prd), env, sto, ite(csq, alt) :: kont)
        case SchemeIf(prd, csq, alt, _) =>
          val (sto1, frame, t1) = pushFrame(prd, env, sto, kont, IteFrame(csq, alt, env), t)
          Set(SchemeState(Control.Ev(prd, env), sto1, frame, t1, ext))

        // (Ev((f x1 x2 ... xn), env, sto, kont) ==> (Ev(f), env, sto, fun(f, x1, ..., xn, bot, ()) :: kont)
        case fun @ SchemeFuncall(f, args, _) =>
          val (sto1, frame, t1) = pushFrame(f, env, sto, kont, FunFrame(fun, args, env), t)
          Set(SchemeState(Control.Ev(f, env), sto1, frame, t1, ext))

        case SchemeLet(bindings, body, _) =>
          evaluateLet(List(), env, sto, kont, bindings, body, t, ext)

        case SchemeLetStar(bindings, body, _) =>
          evaluateLetStar(env, sto, kont, bindings, body, t, ext)

        case SchemeLetrec(bindings, body, _) =>
          val env1 = bindings.map(_._1).foldLeft(env)((newEnv, identifier) => newEnv.extend(identifier.name, alloc(identifier.idn, env, sto, kont, t)))
          evaluateLetrec(Nil, Nil, env1, sto, kont, bindings, body, t, ext)

        // unsupported
        case _: SchemeAssert =>
          Set()

        case _ => throw new Exception("unsupported exception")

    /**
     * Evaluate a literal value, these are evaluated to equivalent representations in the abstract domain. A string literal is allocated in the store
     * at a value address
     */
    private def evalLiteralVal(
        lit: SchemeValue,
        env: Env,
        sto: Sto,
        kont: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
        val (res, sto1) = lit.value match
            case sexp.Value.String(s) =>
              val address = alloc(lit.idn, env, sto, kont, t)
              val sto1 = writeStoV(sto, address, inject(lattice.string(s)))
              (lattice.pointer(address), sto1)

            case sexp.Value.Integer(n)   => (lattice.number(n), sto)
            case sexp.Value.Real(r)      => (lattice.real(r), sto)
            case sexp.Value.Boolean(b)   => (lattice.bool(b), sto)
            case sexp.Value.Character(c) => (lattice.char(c), sto)
            case sexp.Value.Symbol(s)    => (lattice.symbol(s), sto)
            case sexp.Value.Nil          => (lattice.nil, sto)
            case lit                     => throw new Exception(s"Unsupported Scheme literal: $lit")

        Set(SchemeState(Control.Ap(inject(res)), sto1, kont, t, ext))

    private def evalVariable(
        id: Identifier,
        env: Env,
        sto: Sto,
        kont: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
        val res: Val = env
          .lookup(id.name)
          .map(readStoV(sto, _))
          .getOrElse(inject(lattice.bottom))

        Set(SchemeState(Control.Ap(res), sto, kont, t, ext))

    /** Evaluate a non-empty sequence of expression */
    private def evaluate_sequence(
        env: Env,
        sto: Sto,
        kont: Address,
        sequence: List[SchemeExp],
        t: Timestamp,
        ext: Ext
      ): Set[State] =
        assert(!sequence.isEmpty)
        val (sto1, frame, t1) = sequence match
            case List(x) => (sto, kont, t)
            case x :: xs => pushFrame(sequence.head, env, sto, kont, BegFrame(sequence.tail, env), t)

        Set(SchemeState(Control.Ev(sequence.head, env), sto1, frame, t1, ext))

    private def evaluateLet(
        evlBds: List[(Identifier, Val)],
        env: Env,
        sto: Sto,
        kont: Address,
        bindings: List[(Identifier, SchemeExp)],
        body: List[SchemeExp],
        t: Timestamp,
        ext: Ext
      ): Set[State] =
      bindings match
          case List() =>
            val addresses =
              bindings.map(_._1).map((current) => alloc(current.idn, env, sto, kont, t))
            val env1: Env =
              evlBds
                .map(_._1)
                .zip(addresses)
                .foldLeft(env)((envNew, current) => envNew.extend(current._1.name, current._2))
            val sto1: Sto =
              evlBds
                .map(_._2)
                .zip(addresses)
                .foldLeft(sto)((sto, current) => writeStoV(sto, current._2, current._1))

            evaluate_sequence(env1, sto1, kont, body, t, ext)

          case binding :: bindings =>
            val (sto1, frame, t1) = pushFrame(binding._2, env, sto, kont, LetFrame(evlBds, binding :: bindings, body, env), t)
            Set(SchemeState(Control.Ev(binding._2, env), sto1, frame, t1, ext))

    private def evaluateLetStar(
        env: Env,
        sto: Sto,
        kont: Address,
        bindings: List[(Identifier, SchemeExp)],
        body: List[SchemeExp],
        t: Timestamp,
        ext: Ext
      ): Set[State] =
      bindings match
          case List() =>
            // evaluate the body, the environment is already correctly extended by bindings in the previous evaluation steps
            evaluate_sequence(env, sto, kont, body, t, ext)
          case binding :: bindings =>
            // the environment is already extended (or should be) in the "continue" function
            val (sto1, frame, t1) = pushFrame(binding._2, env, sto, kont, LetStarFrame(binding._1, bindings, body, env), t)
            Set(SchemeState(Control.Ev(binding._2, env), sto1, frame, t1, ext))

    private def evaluateLetrec(
        addresses: List[Address],
        values: List[Val],
        env: Env,
        sto: Sto,
        kont: Address,
        bindings: List[(Identifier, SchemeExp)],
        body: List[SchemeExp],
        t: Timestamp,
        ext: Ext
      ): Set[State] =
      bindings match
          case List() =>
            // the enviroment already contains the necessary bindings
            val sto1 = addresses.zip(values).foldLeft(sto)((sto, current) => writeStoV(sto, current._1, current._2))
            evaluate_sequence(env, sto1, kont, body, t, ext)

          case binding :: bindings =>
            val addresses1 = alloc(binding._1.idn, env, sto, kont, t) :: addresses
            val (sto1, frame, t1) = pushFrame(binding._2, env, sto, kont, LetrecFrame(addresses1, values, bindings, body, env), t)
            Set(SchemeState(Control.Ev(binding._2, env), sto1, frame, t1, ext))

    private def applyFun(
        fexp: SchemeFuncall,
        func: Val,
        argv: List[Val],
        env: Env,
        sto: Sto,
        kon: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
        val closures = applyClo(fexp, func, argv, env, sto, kon, t, ext)
        val functions = applyPrim(fexp, func, argv, env, sto, kon, t, ext)
        closures ++ functions

    private def applyClo(
        fexp: SchemeFuncall,
        func: Val,
        argv: List[Val],
        env: Env,
        sto: Sto,
        kon: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
      // TODO: introduce contexts to support things like k-cfa
      lattice.getClosures(project(func)).flatMap {
        case (lam, lex: Env @unchecked) if lam.check(argv.size) =>
          val (sto0, frame, t0) = (sto, kon, t)

          // split in fixed an variable number of arguments
          val (fx, vra) = argv.zip(fexp.args).splitAt(lam.args.length)
          val ctx = () // TODO
          // add the fixed arguments on addresses in the store
          val sto1 = lam.args.zip(fx).foldLeft(sto0) { case (sto, (par, (value, _))) =>
            writeStoV(sto, VarAddr(par.idn, ctx), value)
          }
          // add variable arguments as a list to a particular address in the store
          val sto2 = lam.varArgId match
              case Some(id) =>
                val (vlu, newsto) = allocList(vra, env, sto1, kon, t0)
                writeStoV(newsto, VarAddr(id.idn, ctx), vlu)
              case _ => sto1

          // extend the environment with the correct bindigs
          val pars = (lam.args ++ lam.varArgId.map(List(_)).getOrElse(List()))
          val env1 = pars.foldLeft(env)((env, par) => env.extend(par.name, VarAddr(par.idn, ctx)))
          // and evaluate the body
          evaluate_sequence(env1, sto2, frame, lam.body, t0, ext)
        case (lam, lex) =>
          println(s"Applied with invalid number of arguments ${argv.size}")
          Set()
      }

    /** Apply the given value as a primitive function (if the value is a primitive function) */
    private def applyPrim(
        fexp: SchemeExp,
        func: Val,
        argv: List[Val],
        env: Env,
        sto: Sto,
        kon: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
      lattice.getPrimitives(project(func)).flatMap { name =>
          val primitive = primitives(name)
          given bridge: InterpreterBridge = InterpreterBridge(env, sto, kon, t)
          primitive.callMF(fexp, argv.map(project)) match
              // the primitive is successfull apply the continuation with the value returned from the primitive
              case MayFailSuccess(vlu) =>
                val sto1 = bridge.updatedSto
                Set(SchemeState(Control.Ap(inject(vlu)), sto1, kon, t, ext))
              case MayFailBoth(vlu, _) =>
                val sto1 = bridge.updatedSto
                Set(SchemeState(Control.Ap(inject(vlu)), sto1, kon, t, ext))
              // executing the primitive is unsuccessfull, no successors states are generated
              case MayFailError(_) => Set()
      }

    protected def cond(
        value: Val,
        csq: Expr,
        alt: Expr,
        env: Env,
        sto: Sto,
        kont: Address,
        t: Timestamp,
        ext: Ext
      ): Set[State] =
        import Control.*
        val csqSt = if lattice.isTrue(project(value)) then Set(SchemeState(Ev(csq, env), sto, kont, t, ext)) else Set()
        val altSt = if lattice.isFalse(project(value)) then Set(SchemeState(Ev(alt, env), sto, kont, t, ext)) else Set()
        csqSt ++ altSt

    private def allocList(items: List[(Val, SchemeExp)], env: Env, sto: Sto, kont: Address, t: Timestamp): (Val, Sto) = items match
        case Nil => (inject(lattice.nil), sto)
        case (vlu, exp) :: rest =>
          val (tail, sto1) = allocList(rest, env, sto, kont, t)
          allocCons(exp, vlu, tail, env, sto1, kont, t)

    private def allocCons(
        exp: SchemeExp,
        car: Val,
        cdr: Val,
        env: Env,
        sto: Sto,
        kont: Address,
        t: Timestamp
      ): (Val, Sto) =
        val addr = alloc(exp.idn, env, sto, kont, t) // TODO: check whether a seperate addr is needed for cons
        val sto1 = writeSto(sto, addr, Storable.V(lattice.cons(project(car), project(cdr))))
        (inject(lattice.pointer(addr)), sto1)

    protected def continueWith(sto: Sto, kont: Address)(f: (Address) => SchemeState): Set[State] =
      Set(f(kont))

    protected def continueWiths(sto: Sto, kont: Address)(f: (Address) => Set[SchemeState]): Set[State] =
      f(kont)

    /** Apply the given continuation with the given value */
    def continue(value: Val, sto: Sto, kont: Address, t: Timestamp, ext: Ext): Set[State] =
      (readSto(sto, kont) match { case Storable.K(ks) => ks; case _ => ??? }).flatMap {
        // (Ap(v), env, sto, assgn(x) :: k) ==> (Ap(nil), env, sto', k)
        //    where sto' = sto [ env(x) -> v ]
        case AssFrame(id, env, Some(next)) =>
          val sto1 = writeSto(sto, env.lookup(id.name).get, Storable.V(project(value)))
          continueWith(sto, next)(SchemeState(Control.Ap(inject(lattice.nil)), sto1, _, t, ext))

        // (Ap(v), env, sto, beg(e1 e2 ... en) :: k) ==> (Ev(e1), env, sto, beg(e2 .. en) :: k)
        case BegFrame(e1 :: exps, env, Some(addr)) =>
          continueWith(sto, addr) { kont =>
              val (sto1, frame, t1) = pushFrame(e1, env, sto, kont, BegFrame(exps, env), t)
              SchemeState(Control.Ev(e1, env), sto1, frame, t1, ext)
          }

        // (Ap(v), env, sto, beg() :: k) ==> (Ap(v), env, sto, k)
        case BegFrame(List(), env, Some(addr)) =>
          continueWith(sto, addr) { kont =>
            SchemeState(Control.Ap(value), sto, kont, t, ext)
          }

        // (Ap(true), env, sto, ite(csq, alt) :: k) ==> (Ev(csq), env, sto, k)
        // (Ap(false), env, sto, ite(csq, alt) :: k) ==> (Ev(alt), env, sto, k)
        case IteFrame(csq, alt, env, Some(addr)) =>
          continueWiths(sto, addr)(cond(value, csq, alt, env, sto, _, t, ext))

        // (Ap(fv), env, sto, fun(f, a :: args) :: k) ==> (Ev(a), env, sto, FunArg(f, args, fv, List()) :: k)
        case FunFrame(f, arg :: args, env, Some(addr)) =>
          continueWith(sto, addr) { kont =>
              val (sto1, frame, t1) = pushFrame(arg, env, sto, kont, ArgFrame(f, args, value, List(), env), t)
              SchemeState(Control.Ev(arg, env), sto1, frame, t1, ext)
          }

        // (Ap(fv), env, sto, fun(f, ()) :: k) ==> (Ev(a), env, sto, ret(env) :: k)
        case FunFrame(f, List(), env, Some(addr)) =>
          continueWiths(sto, addr) { kont =>
            applyFun(f, value, List(), env, sto, kont, t, ext)
          }

        case ArgFrame(f, arg :: args, fv, argsV, env, Some(addr)) =>
          continueWith(sto, addr) { kont =>
              val (sto1, frame, t1) = pushFrame(arg, env, sto, kont, ArgFrame(f, args, fv, value :: argsV, env), t)
              SchemeState(Control.Ev(arg, env), sto1, frame, t1, ext)
          }

        case ArgFrame(f, List(), fv, argsV, env, Some(addr)) =>
          continueWiths(sto, addr) { kont =>
            applyFun(f, fv, (value :: argsV).reverse, env, sto, kont, t, ext)
          }

        case LetFrame(evalBds, _ :: bindings, body, env, Some(addr)) =>
          continueWiths(sto, addr) { kont =>
            evaluateLet(evalBds, env, sto, kont, bindings, body, t, ext)
          }

        case LetStarFrame(currentIdentifier, restBindings, body, env, Some(addr)) =>
          continueWiths(sto, addr) { kont =>
              val addr = alloc(currentIdentifier.idn, env, sto, kont, t)
              val env1 = env.extend(currentIdentifier.name, addr)
              val sto1 = writeStoV(sto, addr, value)
              evaluateLetStar(env1, sto1, kont, restBindings, body, t, ext)
          }

        case LetrecFrame(addresses, values, bindings, body, env, Some(addr)) =>
          continueWiths(sto, addr) { kont =>
            evaluateLetrec(addresses, value :: values, env, sto, kont, bindings, body, t, ext)
          }

        case HltFrame => Set()
      }