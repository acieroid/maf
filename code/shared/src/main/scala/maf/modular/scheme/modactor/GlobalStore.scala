package maf.modular.scheme.modactor

import maf.modular.scheme.modflocal.EffectsMC
import maf.core.DynMonad
import maf.core.Monad.*
import maf.modular.scheme.modf.*
import maf.modular.scheme.modf.SchemeModFComponent
import maf.util.Monoid
import maf.util.MonoidImplicits.*
import maf.core.Monad
import maf.modular.scheme.modflocal.EffectsStateM
import maf.language.scheme.*
import maf.modular.ModAnalysis
import maf.language.AScheme.ASchemeLattice
import maf.core.Environment
import maf.core.Address
import maf.core.Identifier
import maf.modular.scheme.PtrAddr
import maf.core.Identity
import maf.modular.scheme.modf.SchemeModFComponent
import maf.language.scheme.primitives.SchemePrimitives
import maf.language.AScheme.ASchemeValues.Behavior
import maf.modular.scheme.VarAddr
import maf.util.benchmarks.Timeout.T
import scala.reflect.ClassTag
import maf.modular.Dependency
import maf.core.MonadStateT
import maf.core.monad.ReaderT
import maf.modular.worklist.FIFOWorklistAlgorithm
import maf.core.StateOps
import maf.core.Lattice
import maf.language.AScheme.ASchemeValues.AID
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.modular.scheme.modf.SchemeModFComponent.Call
import maf.core.worklist.FIFOWorkList
import maf.util.MonoidInstances

class GlobalStoreModActor(prog: SchemeExp)
    extends SchemeModActorSemantics(prog),
      SimpleMessageMailbox,
      PowersetMailboxAnalysis,
      ASchemeConstantPropagationDomain:
    outer =>

    val outerClassTag: ClassTag[Component] = summon[ClassTag[Component]]

    type Context = Unit
    override type Component = ActorAnalysisComponent[Ctx]

    case class IntraState(
        self: Component,
        writes: Set[Dependency] = Set(),
        reads: Set[Dependency] = Set(),
        calls: Set[Component] = Set(),
        mailboxes: Map[Component, Mailbox] = Map(),
        actors: Set[Component] = Set(),
        behaviors: Map[Component, Set[Behavior]] = Map(),
        sto: Map[Address, Value] = Map())

    case class InterState(
        mailboxes: Map[Component, Mailbox] = Map(),
        actors: Set[Component] = Set(),
        behaviors: Map[Component, Set[Behavior]] = Map(),
        sto: Map[Address, Value])

    import maf.core.SetMonad.*

    type State = IntraState
    type Inter = InterState
    type Ctx = Context

    //////////////////////////////////////////////////
    // Components
    //////////////////////////////////////////////////

    def initialComponent: Component =
        ActorAnalysisComponent(MainActor, None, Some(()))

    //
    // Body
    //

    private def enclosingActorBody(cmp: SchemeModActorComponent[Ctx]): SchemeExp = cmp match
        // the main actor is represented by the main Scheme program
        case MainActor => prog
        // otherwise we analyze the body of the behavior of the actor
        case Actor(beh, env, ctx) => beh.bdy
        // All other cases are either not supported or already caught by `body`
        case _ => throw new Exception(s"component $cmp is not supported")

    private def sequentialComponentBody(cmp: SchemeModFComponent): SchemeExp = cmp match
        // A component associated with a regular function call
        case Call((bdy, _), _) => bdy
        // A component associated with the behavior of an actor
        case BehaviorComponent(beh, _, _) => beh.bdy
        // All other cases are either not supported or already caught by `body`
        case _ => throw new Exception(s"component $cmp is not supported.")

    override def body(cmp: Component): SchemeExp = cmp match
        // the initial behavior of an actor
        case ActorAnalysisComponent(enclosingActor, None | Some(SchemeModFComponent.Main), _) =>
            enclosingActorBody(enclosingActor)
        // a function or a new behavior of the actor
        case ActorAnalysisComponent(enclosingActor, Some(sequential), _) =>
            sequentialComponentBody(sequential)

    //
    // Context
    //

    override def componentContext(cmp: Component): Ctx = cmp match
        // the initial behavior of an actor
        case ActorAnalysisComponent(_, _, ctx) =>
            ctx.get

    override def initialCtx: Ctx = ()

    override def newContext(fex: Exp, lam: Lam, ags: List[Val], ctx: Ctx): Ctx = ()

    //
    // Env
    //

    def environment(cmp: ActorAnalysisComponent[Ctx]): Env =
        cmp match
            case ActorAnalysisComponent(MainActor, None | Some(SchemeModFComponent.Main), _) => initialEnv
            case ActorAnalysisComponent(Actor(beh, env, ctx), None | Some(SchemeModFComponent.Main), _) =>
                env
            case ActorAnalysisComponent(_, Some(SchemeModFComponent.Call(clo, ctx)), _) =>
                clo._2
            case ActorAnalysisComponent(_, Some(BehaviorComponent(beh, env, ctx)), _) =>
                env

    //////////////////////////////////////////////////
    // Results
    //////////////////////////////////////////////////

    override def getBehaviors: Map[Component, Set[Behavior]] =
        _result.behaviors

    override def getMailboxes: Map[Component, Mailbox] =
        _result.mailboxes

    //////////////////////////////////////////////////
    // ModAnalysis
    //////////////////////////////////////////////////

    // TODO: abstract this in a seperate trait, and provide a mixin
    override val emptyWorklist = FIFOWorkList.empty

    override lazy val initialInterState: Inter =
        InterState(sto = initialSto)

    override lazy val initialEnv: Env =
        Environment(primitives.allPrimitives.map { case (name, vlu) =>
            name -> PrimAddr(name)
        })

    override lazy val initialSto: Map[Address, Value] =
        primitives.allPrimitives.map { case (name, vlu) =>
            PrimAddr(name) -> lattice.primitive(name)
        }.toMap

    override def injectInter(inter: Inter, cmp: Component): DynMonad[Value, EffectsMC[Component, Intra]] =
        import analysisM.*
        val m: A[Value] = for
            // insert the store into the analysis
            _ <- get.map(lens.modify(lens.sto)(_ => inter.sto)) >>= put
            // put the correct mailbox
            _ <- get.map(lens.modify(lens.mailboxes)(_ => inter.mailboxes)) >>= put
            // then evalute the expression
            v <- eval(body(cmp))
        yield v

        DynMonad.from(m)

    def syncInter(vlu: Value, intra: Intra, inter: Inter): Inter =
        // join the global stores together
        val sto = intra.sto.foldLeft(inter.sto) { case (acc, (key, vlu)) =>
            acc + (key -> lattice.join(inter.sto.get(key).getOrElse(lattice.bottom), vlu))
        }

        inter.copy(sto = sto,
                   mailboxes = intra.mailboxes,
                   behaviors = MonoidInstances.mapMonoid.append(inter.behaviors, intra.behaviors),
                   actors = inter.actors ++ intra.actors
        )

    //////////////////////////////////////////////////
    // Monad Instance
    //////////////////////////////////////////////////

    type Reader = [Y] =>> ReaderT[Set, (Ctx, Env), Y]
    type A[X] = MonadStateT[IntraState, Reader, X]

    given lens: ActorLens[IntraState] = new ActorLens[IntraState] {
        //
        // Store
        //
        def putSto(st: IntraState, sto: Map[Address, Value]): IntraState =
            st.copy(sto = sto)
        def getSto(st: IntraState): Map[Address, Value] =
            st.sto

        //
        // Mailboxes
        //
        def putMailboxes(st: IntraState, mb: Map[Component, Mailbox]): IntraState =
            st.copy(mailboxes = mb)
        def getMailboxes(st: IntraState): Map[Component, Mailbox] =
            st.mailboxes

        //
        // Set of actors spawned
        //
        def putActors(st: IntraState, actors: Set[Component]): IntraState =
            st.copy(actors = actors)
        def getActors(st: IntraState): Set[Component] =
            st.actors

        //
        // Set of behaviors discovered during the sequential intra-analysis
        //
        def putBehaviors(st: IntraState, behs: Map[Component, Set[Behavior]]): IntraState =
            st.copy(behaviors = behs)
        def getBehaviors(st: IntraState): Map[Component, Set[Behavior]] =
            st.behaviors

        /** "write" effects */
        def putWrites(s: IntraState, w: Set[Dependency]): IntraState =
            s.copy(writes = w)
        def getWrites(s: IntraState): Set[Dependency] =
            s.writes

        /** "read" effects */
        def putReads(s: IntraState, w: Set[Dependency]): IntraState =
            s.copy(reads = w)
        def getReads(s: IntraState): Set[Dependency] =
            s.reads

        /** "call" effects */
        def putCalls(s: IntraState, c: Set[Component]): IntraState =
            s.copy(calls = c)
        def getCalls(s: IntraState): Set[Component] = s.calls

        /** access to a field called "self" */
        def getSelfCmp(s: IntraState): Component =
            s.self
    }

    protected val monadInstance: StateOps[IntraState, A] = MonadStateT.stateInstance[IntraState, Reader]
    implicit val analysisM = new ModularAnalysisM with EffectsStateM[A, Component, IntraState] {
        given componentGiven: ClassTag[Component] = outer.outerClassTag

        export monadInstance.*
        import monadInstance.*
        import maf.core.monad.MonadLift.*
        def getEnv: A[Env] = map(lift(ReaderT.ask))(_._2)
        def getCtx: A[Ctx] = map(lift(ReaderT.ask))(_._1)
        def selfActor: A[ActorRef] = ???
        def selfActorCmp: A[Component] =
            get.map(_.self)
        def mbottom[X]: A[X] =
            lift(ReaderT.lift(Set()))
        def mjoin[X: Lattice](x: A[X], y: A[X]): A[X] =
            // in this lattice we do not join
            nondets(List(x, y))
        def allocateCall(lam: Lam, env: Environment[Address]): A[Component] =
            for
                ctx <- getCtx
                cmp <- selfActorCmp
            yield ActorAnalysisComponent(cmp.enclosingActor, Some(SchemeModFComponent.Call((lam, env), None)), Some(ctx))

        def allocateBehavior(beh: Behavior, idn: Identity): A[Component] =
            for
                // TODO: allocate some context
                ctx <- getCtx
                cmp <- selfActorCmp
                // TODO: expand environment? check with the code in the semantics
                env <- getEnv
            yield ActorAnalysisComponent(cmp.enclosingActor, Some(BehaviorComponent(beh, env, None)), Some(ctx))

        def allocateActor(initialBehavior: Behavior, idn: Identity): A[Component] =
            // TODO: allocate context?
            for ctx <- getCtx
            yield ActorAnalysisComponent(Actor(initialBehavior, initialBehavior.lexEnv, ()), None, Some(ctx))

        def nondets[X](xs: Iterable[A[X]]): A[X] =
            MonadStateT((s) => ReaderT((e) => xs.toList.foldMap(_.run(s).runReader(e))))

        def withEnv[X](f: Env => Env)(blk: A[X]): A[X] =
            MonadStateT((s) => ReaderT.local[Set, (Ctx, Env), (X, IntraState)] { case (ctx, env: Env) => (ctx, f(env)) }(blk.run(s)))

        def withCtx[X](f: Ctx => Ctx)(blk: A[X]): A[X] =
            MonadStateT((s) => ReaderT.local[Set, (Ctx, Env), (X, IntraState)] { case (ctx, env: Env) => (f(ctx), env) }(blk.run(s)))

        def fail[X](err: maf.core.Error): A[X] = mbottom

        /**
         * Runs the analysis represented by `m` for the given `cmp`.
         *
         * @note
         *   it is expected that `m` is a computation that injects the correct store and environment
         */
        def run[X](cmp: Component, m: A[X]): Set[(X, IntraState)] =
            val st = IntraState(self = cmp)
            val ev = (componentContext(cmp), environment(cmp))
            m.run(st).runReader(ev)

    }

    override def view(cmp: Component): SchemeModActorComponent[Context] = ???