package maf.aam

import maf.core.*

/** Provides functionality for a full AAM style analysis */
trait AAMAnalysis:
    /** The type of the environment that should be used in the analysis */
    type Env

    /** The type of the closure that should be used in the analysis */
    type Clo

    /** The type of continuation that should be used in the analysis */
    type Kont

    /** The type of state that should be used in the analysis. */
    type State

    /** The type of expression to use in the analysis */
    type Expr

    /** The type of the timestamp in the analysis */
    type Timestamp

    /** The type of the store */
    type Sto

    /** A set of seen states in the analysis */
    private var seen: Set[State] = Set()

    /** Initial timestamp */
    val initialTime: Timestamp

    /** Tick the time forward */
    def tick(timestamp: Timestamp, env: Env, sto: Sto, kont: Address): Timestamp

    /** Inject the expression into the analysis state */
    def inject(expr: Expr): State

    /** Step the analysis state */
    def step(start: State): Set[State]

    /** Invalidate the set of seen states */
    def invalidate(): Unit =
      seen = Set()

    /** Allocate a fresh address in the store */
    def alloc(identity: Identity, env: Env, sto: Sto, kont: Address, ctx: Timestamp): Address

    /** Analyze the given expression and return the set of (non-invalid) state */
    def analyze(expr: Expr): Set[State] =
        val s0 = inject(expr)
        var todo: Set[State] = Set() // states to (potentially) analyze

        while (!(todo -- seen).isEmpty) do
            todo = (todo -- seen)
            seen = seen ++ todo
            todo = todo.flatMap(step)

        seen
