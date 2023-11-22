package maf.cli.runnables

import java.io.{BufferedReader, InputStreamReader}
import java.util.concurrent.*
import maf.language.scheme.interpreter.*
import maf.language.scheme.primitives.*
import maf.bench.scheme.*
import scala.concurrent.duration.Duration
import maf.language.scheme.interpreter.ConcreteValues._
import maf.util.benchmarks.Timeout
import maf.util.*
import maf.language.scheme.*
import maf.core.*
import java.util.concurrent.TimeoutException

/*
 * TODO:
 * - check how many run to completion
 * - check how many disagree on timeout
 * - store/show output diffs
 * - printing vectors: #(elements)
 */

class ExternalInterpreter(val executableName: String):
    def run(program: SchemeExp, timeoutSeconds: Int): String =
      // Write the file
      val w = Writer.open("/tmp/foo.scm")
      Writer.write(w, program.toString)
      Writer.close(w)
      // Run the executable on the file with a timeout
      val p = Runtime.getRuntime().nn.exec(executableName + " /tmp/foo.scm").nn
      val output = new BufferedReader(new InputStreamReader(p.getInputStream()))
      if (!p.waitFor(timeoutSeconds, TimeUnit.SECONDS)) then
        p.destroy()
        throw new TimeoutException("Interpreter ran for too long")
      else
        val result = LazyList.continually(output.readLine()).takeWhile(_ != null).mkString("\n")
        if p.exitValue != 0 then
          val errorReader = new BufferedReader(new InputStreamReader(p.getErrorStream()))
          val error = LazyList.continually(errorReader.readLine()).takeWhile(_ != null).mkString("\n")
          throw new Exception(error)
        else result


trait Disagreement:
    val program: String
    def dump(outDir: String): Unit

case class OutputDisagreement(val program: String, val firstOutput: String, val secondOutput: String) extends Disagreement:
    def dump(outDir: String): Unit =
      println(s"${program}: different output (see $outDir for details)")
      val programName = program.replaceAll("/", "-").nn
      val w1 = Writer.open(s"$outDir/$programName.first")
      Writer.write(w1, firstOutput)
      Writer.close(w1)
      val w2 = Writer.open(s"$outDir/$programName.second")
      Writer.write(w2, secondOutput)
      Writer.close(w2)
case class TimeoutDisagreement(val program: String, val firstTimesOut: Boolean) extends Disagreement:
    def dump(outDir: String): Unit =
      val desc = if firstTimesOut then "first" else "second"
      println(s"${program}: ${desc} times out")
case class CrashDisagreement(val program: String, val error: String) extends Disagreement:
    def dump(outDir: String): Unit =
      println(s"${program}: ${error.take(10)} (see $outDir for details)")
      val programName = program.replaceAll("/", "-").nn
      val w = Writer.open(s"$outDir/$programName.error")
      Writer.writeln(w, error)
      Writer.close(w)

trait InterpreterComparison:
    def instrument(program: SchemeExp): SchemeExp = program

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement]

    def compareResults[A](name: String, first: Either[Throwable, A], second: Either[Throwable, A], cmp: (A, A) => Option[Disagreement]): Option[Disagreement] =
       (first, second) match
        case (Left(_: TimeoutException), Left(_: TimeoutException)) => None
        case (Right(v1), Right(v2)) => cmp(v1, v2)
        case (Left(_: TimeoutException), _: Right[_, _]) => Some(TimeoutDisagreement(name, true))
        case (_: Right[_, _], Left(_: TimeoutException)) => Some(TimeoutDisagreement(name, false))
        case (Left(exc), _: Right[_, _]) => Some(CrashDisagreement(name, exc.toString()))
        case (_: Right[_, _], Left(exc)) => Some(CrashDisagreement(name, exc.toString()))
        case _ =>
          println("!!! Both crashed, this is likely an invalid benchmark")
          Some(CrashDisagreement(name, "Both crashed!"))

    /* Remove unique part of the address, to keep only its identity */
    def strip(v: ConcreteValues.Value): ConcreteValues.Value =
      import ConcreteValues.Value._
      v match
        case Clo(lambda, env) => Clo(lambda, env.map((name, addr) => (name, (-1, addr._2))))
        case Pointer((_, identity)) => Pointer((-1, identity))
        case Cons(car, cdr) => Cons(strip(car), strip(cdr))
        case Vector(size, elems, init) => Vector(size, elems.map((idx, value) => (idx, strip(value))), strip(init))
        case _ => v

class PrintBasedInterpreterComparison extends InterpreterComparison:
    val io = new PrintIO()
    val interpreter1 = new ExternalInterpreter("guile")
    val interpreter2 = new SchemeInterpreter((_, _) => (), io)
    val timeoutSeconds: Int = 10

    def runInternalInterpreter(program: SchemeExp): Either[Throwable, String] =
      try
        interpreter2.run(program, Timeout.start(Duration(timeoutSeconds, "seconds")))
        Right(io.getAndClearOutput())
      catch case exc: Throwable => Left(exc)

    def runExternalInterpreter(program: SchemeExp): Either[Throwable, String] =
      try Right(interpreter1.run(program, timeoutSeconds))
      catch case exc: Throwable => Left(exc)

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
      compareResults(name, runInternalInterpreter(program), runExternalInterpreter(program),
                     (v1: String, v2: String) => if v1.trim() == v2.trim() then None else Some(OutputDisagreement(name, v1, v2)))

class InstrumentationBasedInterpreterComparison extends PrintBasedInterpreterComparison:
    override def instrument(program: SchemeExp): SchemeExp = program match {
      case SchemeLambda(name, args, body, annotation, idn) =>
        SchemeLambda(name, args, body.map(instrument), annotation, idn)
      case SchemeVarArgLambda(name, args, vararg, body, annotation, idn) =>
        SchemeVarArgLambda(name, args, vararg, body.map(instrument), annotation, idn)
      case SchemeFuncall(f, args, idn) =>
        SchemeFuncall(SchemeVar(Identifier("__log", idn)),
                        List(SchemeFuncall(instrument(f), args.map(instrument), idn)),
                        idn)
      case SchemeIf(cond, cons, alt, idn) =>
        SchemeIf(instrument(cond), instrument(cons), instrument(alt), idn)
      case SchemeLet(bindings, body, idn) =>
        SchemeLet(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
      case SchemeLetStar(bindings, body, idn) =>
        SchemeLetStar(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
      case SchemeLetrec(bindings, body, idn) =>
        SchemeLetrec(bindings.map(b => (b._1, instrument(b._2))), body.map(instrument), idn)
      case SchemeSet(variable, value, idn) =>
        SchemeSet(variable, instrument(value), idn)
      case SchemeSetLex(variable, lexAddr, value, idn) =>
        SchemeSetLex(variable, lexAddr, instrument(value), idn)
      case SchemeBegin(exps, idn) =>
        SchemeBegin(exps.map(instrument), idn)
      case SchemeDefineVariable(name, value, idn) =>
        SchemeDefineVariable(name, instrument(value), idn)
      case SchemeAssert(exp, idn) =>
        SchemeAssert(instrument(exp), idn)
      case _ => program
    }

class ReturnValueInterpreterComparison extends InterpreterComparison:
    val interpreter1: BaseSchemeInterpreter[_] = new CPSSchemeInterpreter();
    val interpreter2: BaseSchemeInterpreter[_] = new SchemeInterpreter();
    val timeout: Duration = Duration(10, "seconds")

    def runInterpreter(interpreter: BaseSchemeInterpreter[_], program: SchemeExp): Either[Throwable, Value] =
      try Right(interpreter.run(program, Timeout.start(timeout)))
      catch case exc: Throwable => Left(exc)

    def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
      compareResults(name, runInterpreter(interpreter1, program), runInterpreter(interpreter2, program),
                     (v1: Value, v2: Value) => if (strip(v1) == strip(v2)) then None else Some(OutputDisagreement(name, v1.toString, v2.toString)))

class CallbackBasedInterpreterComparison extends ReturnValueInterpreterComparison:

    def generateCallback: ((Identity, ConcreteValues.Value) => Unit, () => Map[Identity, Set[ConcreteValues.Value]]) =
      var seen: Map[Identity, Set[ConcreteValues.Value]] = Map()
      ((id, v) => seen = seen + (id -> (seen.get(id).getOrElse(Set()) + v)),
       () => seen)

    def findDifference(m1: Map[Identity, Set[Value]], m2: Map[Identity, Set[Value]]): Option[(Identity, String, String)] =
        for (k1, v1) <- m1 do
          val v2: Option[Set[ConcreteValues.Value]] = m2.get(k1)
          if v2.isDefined == false || v2.get.map(strip) != v1.map(strip) then
            return Some((k1, v1.toString, v2.map(_.toString).getOrElse("absent")))
        None

    override def differenceOn(name: String, program: SchemeExp): Option[Disagreement] =
      val callback1 = generateCallback
      val interpreter1 = new CPSSchemeInterpreter(callback1._1)
      val callback2 = generateCallback
      val interpreter2 = new SchemeInterpreter(callback2._1)
      compareResults(name, runInterpreter(interpreter1, program), runInterpreter(interpreter2, program),
                     (v1, v2) =>
                        findDifference(callback1._2(), callback2._2())
                                      .orElse(findDifference(callback2._2(), callback1._2()))
                                      .map(diff => OutputDisagreement(name, s"${diff._1}: ${diff._2}", s"${diff._1}: ${diff._3}")))

class DeltaDebug(comparison: InterpreterComparison):

    val benchmarks = SchemeBenchmarkPrograms.sequentialBenchmarks.take(25)
    var disagreements: List[Disagreement] = List()

    def parseProgram(txt: String): SchemeExp =
      val parsed = SchemeParser.parse(txt)
      val instrumented = parsed.map(comparison.instrument)
      val preluded = SchemePrelude.addPrelude(instrumented, incl = Set("assert", "__log"))
      SchemeParser.undefine(preluded)

    def onBenchmark(name: String): Unit =
      println(s"Running on $name")
      val content = Reader.loadFile(name)
      val program = parseProgram(content)
      comparison.differenceOn(name, program) match {
        case Some(disagreement) =>
          println(s"Disagreement on $name")
          disagreements = disagreement :: disagreements
        case _ => ()
      }

    def report(): Unit =
      println(s"I ran ${benchmarks.size} benchmarks and found ${disagreements.length} disagreements")
      val outputDisagreements = disagreements.filter(_.isInstanceOf[OutputDisagreement])
      println(s"Output disagreements: ${outputDisagreements.length} (raw outputs in in /tmp/out)")
      outputDisagreements.foreach(_.dump("/tmp/out/"))
      val timeoutDisagreements = disagreements.filter(_.isInstanceOf[TimeoutDisagreement])
      println("Timeout disagreements: ${timeoutDisagreements.length}")
      timeoutDisagreements.foreach(_.dump("/tmp/out/"))
      val crashDisagreements = disagreements.filter(_.isInstanceOf[CrashDisagreement])
      println("Crash disagreements:: ${crashDisagreements.length}")
      crashDisagreements.foreach(_.dump("/tmp/out/"))

    def main(args: Array[String]): Unit =
      benchmarks.foreach(onBenchmark)
      report()

object DeltaDebugExternal extends DeltaDebug(new InstrumentationBasedInterpreterComparison)
object DeltaDebugInternal extends DeltaDebug(new CallbackBasedInterpreterComparison)
