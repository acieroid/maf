package maf.test.language.scheme

import org.scalatest.flatspec.AnyFlatSpec
import maf.language.scheme.interpreter.*
import maf.language.scheme.*
import maf.util.benchmarks.Timeout

class PrintTest extends AnyFlatSpec:
    val io = new PrintIO()
    val interpreter = new SchemeInterpreter((_, _) => (), io)

    val programsAndOutputs: List[(String, String)] = List(
      ("(display 'hello)" -> "hello"),
      ("(display \"hello\")" -> "hello"),
      ("(display \"\\\"\")" -> "\""),
      ("(display \"\\n\")" -> "\n"),
      ("(display #\\h)" -> "h"),
      ("(display '())" -> "()"),
      ("(display (cons 'a 'b))" -> "(a . b)"),
      ("(display (cons 'a '()))" -> "(a)"),
      ("(display (cons 'a (cons 'b '())))" -> "(a b)"),
    )

    def test(program: String, expectedOutput: String): Unit =
       "display" should s"display as a Scheme interpreter for $program" in {
         interpreter.run(SchemeParser.undefine(SchemeParser.parse(program)), Timeout.none)
         assertResult(expectedOutput) { io.getAndClearOutput() }
       }

    programsAndOutputs.foreach((programAndOutput: (String, String)) =>
      test(programAndOutput._1, programAndOutput._2))
