package maf.test.aam

import maf.test.modular.scheme.SchemeSoundnessTests
import maf.language.scheme.*
import maf.language.scheme.primitives.*
import maf.aam.SchemeAAMSemantics
import maf.aam.{AAMAnalysis, GraphElementAAM}
import maf.aam.SchemeAAMContextInsensitivity
import maf.aam.SchemeAAMAnalysisResults
import maf.modular.scheme.SchemeConstantPropagationDomain
import maf.test.VariousSequentialBenchmarks
import maf.test.JSS2021Benchmarks
import maf.util.benchmarks.Timeout

import scala.concurrent.duration._
import maf.util.graph.*

trait DotGraphOutput extends AAMSoundnessTests:
    final val graph = new DotGraph[GraphElementAAM, GraphElement]()

    type G = graph.G
    type N = GraphElementAAM
    type E = GraphElement

    implicit protected def graphInstance = graph.G.typeclass
    protected def emptyGraph = graph.G.typeclass.empty
    protected def saveGraph(benchmark: Benchmark, graph: G): Unit =
        val outName = s"${benchmark.replace("/", "_")}.dot"
        graph.toFile(outName)

trait SchemeAAMSoundnessTests extends maf.test.aam.AAMSoundnessTests with DotGraphOutput:
    override def parseProgram(txt: String): SchemeExp =
        val parsed = SchemeParser.parse(txt)
        val prelud = SchemePrelude.addPrelude(parsed, incl = Set("__toplevel_cons", "__toplevel_cdr", "__toplevel_set-cdr!"))
        val transf = SchemeMutableVarBoxer.transform(prelud)
        SchemeParser.undefine(transf)

class SchemeInsensitiveSoundnessTests extends SchemeAAMSoundnessTests with VariousSequentialBenchmarks:

    override val name: String = "Scheme AAM soundness tests"
    override def benchmarks: Set[Benchmark] = Set(
      "test/R5RS/various/fact.scm"
    )
    override def analysisTimeout(b: Benchmark): Timeout.T = Timeout.start(Duration(12, SECONDS))
    override def analysis(b: SchemeExp): Analysis =
      new SchemeAAMSemantics(b) with AAMAnalysis with SchemeAAMAnalysisResults with SchemeAAMContextInsensitivity with SchemeConstantPropagationDomain
