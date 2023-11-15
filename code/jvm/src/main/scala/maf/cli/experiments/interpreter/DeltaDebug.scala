package maf.cli.runnables

import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.*
import maf.bench.scheme.*
import scala.concurrent.duration.Duration
import maf.language.scheme.interpreter.ConcreteValues._
import maf.util.benchmarks.Timeout
import maf.util.*
import maf.language.scheme.*
import java.util.concurrent.TimeoutException

/* Potential ideas:
 * - How to detect mismatches between two interpreters?
 *   - We can instrument the interpreter (or the program directly) to print all/a subset of the evaluations, and compare that
 *   - They should agree on timing out (or not?)
 * TODO:
 * - use callback to interpreter
 * - run on all 256 benchmarks
 * - check how many run to completion
 * - check how many disagree on timeout
 */

trait InterpreterComparison:
    def agreeOn(program: SchemeExp): Boolean

object ReturnValueInterpreterComparison extends InterpreterComparison:
    val interpreter1: BaseSchemeInterpreter[_] = new CPSSchemeInterpreter();
    val interpreter2: BaseSchemeInterpreter[_] = new SchemeInterpreter();
    val timeout: Duration = Duration(10, "seconds")

    def runInterpreter(interpreter: BaseSchemeInterpreter[_], program: SchemeExp): Option[Value] =
      try
        Some(interpreter.run(program, Timeout.start(timeout)))
      catch case exc: TimeoutException =>
        None

    def agreeOn(program: SchemeExp): Boolean =
      (runInterpreter(interpreter1, program), runInterpreter(interpreter2, program)) match {
        case (None, None) => false /* both time out */
        case (Some(v1), Some(v2)) => v1 == v2
        case _ => false /* one time out, the other not */
      }



object DeltaDebug:

    val comparison = ReturnValueInterpreterComparison

    def parseProgram(txt: String): SchemeExp =
        val parsed = SchemeParser.parse(txt)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        SchemeParser.undefine(transf)

    def onBenchmark(name: String): Unit =
      println(s"Running on $name")
      val content = Reader.loadFile(name)
      val program = parseProgram(content)
      if (!comparison.agreeOn(program)) then println(s"Different results on $name")

    def main(args: Array[String]): Unit =
      SchemeBenchmarkPrograms.gambit.foreach(onBenchmark)
