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
 * - fix toStringification of our concrete interpretrer values
 * - instrumentation-based comparison: replace any function call by something that logs the args, calls the function, logs the result
 *
 * (foo 1 2 3)
 * becomes
 * (log (foo (log 1) (log 2) (log 3)))
 * apply it after parsing + preluding, dump it back to file
 * but what does log do? In our interpreter, we can have a specific primitive
 * We could also simply log the output and display within log
 *
 * Bugs found:
 * Running on test/R5RS/icp/icp_6_stopandcopy_scheme.scm
[error] UninitialisedVariableError(cons)
[error] 	at maf.language.scheme.interpreter.ProgramError$.apply(BaseSchemeInterpreter.scala:10)
[error] 	at maf.language.scheme.interpreter.BaseSchemeInterpreter.signalException(BaseSchemeInterpreter.scala:107)
[error] 	at maf.language.scheme.interpreter.BaseSchemeInterpreter.signalException$(BaseSchemeInterpreter.scala:14)
[error] 	at maf.language.scheme.interpreter.CPSSchemeInterpreter.signalException(CPSSchemeInterpreter.scala:12)
[error] 	at maf.language.scheme.interpreter.CPSSchemeInterpreter.eval(CPSSchemeInterpreter.scala:184)
 */

trait InterpreterComparison:
    def differenceOn(program: SchemeExp): Option[String]

    /* Remove unique part of the address, to keep only its identity */
    def strip(v: ConcreteValues.Value): ConcreteValues.Value =
      import ConcreteValues.Value._
      v match
        case Clo(lambda, env) => Clo(lambda, env.map((name, addr) => (name, (-1, addr._2))))
        case Pointer((_, identity)) => Pointer((-1, identity))
        case Cons(car, cdr) => Cons(strip(car), strip(cdr))
        case Vector(size, elems, init) => Vector(size, elems.map((idx, value) => (idx, strip(value))), strip(init))
        case _ => v

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
          val error = new BufferedReader(new InputStreamReader(p.getErrorStream()))
          println(LazyList.continually(error.readLine()).takeWhile(_ != null).mkString("\n"))
          // System.exit(1)
          throw new Exception("external interpreter crashed")
        else result

object PrintBasedInterpreterComparison extends InterpreterComparison:
    val io = new PrintIO()
    val interpreter1 = new ExternalInterpreter("guile")
    val interpreter2 = new SchemeInterpreter((_, _) => (), io)
    val timeoutSeconds: Int = 10

    def runInternalInterpreter(program: SchemeExp): Option[String] =
      try
        interpreter2.run(program, Timeout.start(Duration(timeoutSeconds, "seconds")))
        Some(io.getAndClearOutput())
      catch case exc: Throwable => println(exc) ; None

    def runExternalInterpreter(program: SchemeExp): Option[String] =
      try Some(interpreter1.run(program, timeoutSeconds))
      catch case exc: Throwable => None

    def differenceOn(program: SchemeExp): Option[String] =
      (runInternalInterpreter(program), runExternalInterpreter(program)) match
        case (None, None) => None /* both crash or time out */
        case (Some(v1), Some(v2)) => if (v1 == v2) then None else Some(s"Different output: $v1 != $v2")
        case (None, Some(_)) => Some(s"Internal crashes or times out")
        case (Some(_), None) => Some(s"External crashes or times out")

class ReturnValueInterpreterComparison extends InterpreterComparison:
    val interpreter1: BaseSchemeInterpreter[_] = new CPSSchemeInterpreter();
    val interpreter2: BaseSchemeInterpreter[_] = new SchemeInterpreter();
    val timeout: Duration = Duration(10, "seconds")

    def runInterpreter(interpreter: BaseSchemeInterpreter[_], program: SchemeExp): Option[Value] =
      try
        Some(interpreter.run(program, Timeout.start(timeout)))
      catch case exc: Throwable =>
        None

    def differenceOn(program: SchemeExp): Option[String] =
      (runInterpreter(interpreter1, program), runInterpreter(interpreter2, program)) match
        case (None, None) => None /* both crash or time out */
        case (Some(v1), Some(v2)) => if (strip(v1) == strip(v2)) then None else Some(s"Different return value: $v1 != $v2")
        case _ => Some(s"One crashes or times out, not the other")

object CallbackInterpreterComparison extends ReturnValueInterpreterComparison:

    def generateCallback: ((Identity, ConcreteValues.Value) => Unit, () => Map[Identity, Set[ConcreteValues.Value]]) =
      var seen: Map[Identity, Set[ConcreteValues.Value]] = Map()
      ((id, v) => seen = seen + (id -> (seen.get(id).getOrElse(Set()) + v)),
       () => seen)

    def findDifference(m1: Map[Identity, Set[Value]], m2: Map[Identity, Set[Value]]): Option[String] =
        for (k1, v1) <- m1 do
          val v2: Option[Set[ConcreteValues.Value]] = m2.get(k1)
          if v2.isDefined == false || v2.get.map(strip) != v1.map(strip) then
            return Some(s"difference on key $k1, v1: $v1, v2: ${v2.map(_.toString).getOrElse("absent")}")
        None

    override def differenceOn(program: SchemeExp): Option[String] =
      val callback1 = generateCallback
      val interpreter1 = new CPSSchemeInterpreter(callback1._1)
      val callback2 = generateCallback
      val interpreter2 = new SchemeInterpreter(callback2._1)
      (runInterpreter(interpreter1, program), runInterpreter(interpreter2, program)) match
        case (Some(_), Some(_)) =>
          /* both terminate, let's check their seen values */
          findDifference(callback1._2(), callback2._2()).orElse(findDifference(callback2._2(), callback1._2()))
        case _ => None


object DeltaDebug:

    //val comparison = new ReturnValueInterpreterComparison
    // val comparison = CallbackInterpreterComparison
    val comparison = PrintBasedInterpreterComparison

    def parseProgram(txt: String): SchemeExp =
        val parsed = SchemeParser.parse(txt)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!", "assert"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        SchemeParser.undefine(transf)

    def onBenchmark(name: String): Unit =
      println(s"Running on $name")
      val content = Reader.loadFile(name)
      val program = parseProgram(content)
      comparison.differenceOn(program) match {
        case Some(reason) => println(s"Different results on $name: $reason")
        case _ => ()
      }

    def main(args: Array[String]): Unit =
      SchemeBenchmarkPrograms.sequentialBenchmarks.foreach(onBenchmark)
