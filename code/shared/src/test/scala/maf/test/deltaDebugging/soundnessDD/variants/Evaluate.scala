package maf.test.deltaDebugging.soundnessDD.variants

import maf.test.deltaDebugging.soundnessDD.SoundnessDDTester
import maf.test.deltaDebugging.soundnessDD.variants.baseline.SaveBaseline
import maf.test.deltaDebugging.soundnessDD.variants.counting.{CountingDD, SaveCounting}
import maf.test.deltaDebugging.soundnessDD.variants.deadCode.SaveDeadCode
import maf.test.deltaDebugging.soundnessDD.variants.parallel.SaveParallel
import maf.test.deltaDebugging.soundnessDD.variants.profiling.SaveProfiling
import maf.test.deltaDebugging.soundnessDD.variants.transforming.{SaveTransforming, SchemeModFLocalAdaptiveTests1, TransformingDD}
import maf.util.benchmarks.Statistics

object Evaluate:
  def main(args: Array[String]): Unit = {
    SaveBaseline.save()
    SaveTransforming.save()
    SaveCounting.save()
    SaveParallel.save()
    SaveProfiling.save()
    SaveDeadCode.save()
  }

  def save(tests: List[SoundnessDDTester], dataCollectorString: String, dataCollector: DataCollector): Unit = {
    println("writing to disk")
    dataCollector.writeTo(dataCollectorString)
  }

  def RQ1(baselineData: List[ReductionData],
          transformingData: List[ReductionData],
          countingData: List[ReductionData],
          parallelData: List[ReductionData],
          profilingData: List[ReductionData],
          deadCodeData: List[ReductionData]
         ): Unit =

    def createRow(data: List[ReductionData]): Unit =
      val reductionPercentages = data.map(r => r.reductionPercentage)
      val avgReductionPercentage = Statistics.median(reductionPercentages)
      val stdReductionPercentage = Statistics.stddev(reductionPercentages)

      println("median reduction %: " + avgReductionPercentage + " +- " + stdReductionPercentage)

    println("RQ1")
    createRow(baselineData)
    createRow(transformingData)
    createRow(countingData)
    createRow(parallelData)
    createRow(profilingData)
    createRow(deadCodeData)

  def RQ2(baselineData: List[ReductionData],
          transformingData: List[ReductionData],
          countingData: List[ReductionData],
          parallelData: List[ReductionData],
          profilingData: List[ReductionData],
          deadCodeData: List[ReductionData]): Unit =

    def createRow(data: List[(ReductionData, ReductionData)]): Unit =
      val oracleRatio = data.map(tpl => tpl._1.oracleTreeSizes.size.toDouble / tpl._2.oracleTreeSizes.size)
      val avgOracleRatio = Statistics.median(oracleRatio)
      val stdOracleRatio = Statistics.stddev(oracleRatio)

      val reductionTimeRatio = data.map(tpl => tpl._1.reductionTime.toDouble / tpl._2.reductionTime)
      val avgReductionTimeRatio = Statistics.median(reductionTimeRatio)
      val stdReductionTimeRatio = Statistics.stddev(reductionTimeRatio)

      println("median oracle ratio: "+ avgOracleRatio + " +- " + stdOracleRatio)
      println("median reduction time ratio: " + avgReductionTimeRatio + " +- " + stdReductionTimeRatio)
      println("")

    def createBoxplot(data: List[(ReductionData, ReductionData)]): Unit =
      println("boxplot...")
      val reductionTimeRatio = data.map(tpl => tpl._1.reductionTime.toDouble / tpl._2.reductionTime)
      reductionTimeRatio.foreach(println)

    println("RQ2")
    createRow(baselineData.zip(baselineData))
    createRow(transformingData.zip(baselineData))
    createRow(countingData.zip(baselineData))
    createRow(parallelData.zip(baselineData))
    createRow(profilingData.zip(baselineData))
    createRow(deadCodeData.zip(baselineData))

    //createBoxplot(transformingData.zip(baselineData))
    //createBoxplot(transformingData.zip(countingData))
    //createBoxplot(countingData.zip(parallelData))


object ReaderAndAnalyzeData {
  def main(args: Array[String]): Unit = {
    val baselineDataCollector: DataCollector = DataCollector.readObject("baselineDataCollector")
    val transformingDataCollector: DataCollector = DataCollector.readObject("transformingDataCollector")
    val countingDataCollector: DataCollector = DataCollector.readObject("countingDataCollector")
    val parallelDataCollector: DataCollector = DataCollector.readObject("parallelDataCollector")
    val profilingDataCollector: DataCollector = DataCollector.readObject("profilingDataCollector")
    val deadCodeDataCollector: DataCollector = DataCollector.readObject("deadCodeDataCollector")

    Evaluate.RQ1(
      baselineDataCollector.reductionData,
      transformingDataCollector.reductionData,
      countingDataCollector.reductionData,
      parallelDataCollector.reductionData,
      profilingDataCollector.reductionData,
      deadCodeDataCollector.reductionData
    )

    Evaluate.RQ2(
      baselineDataCollector.reductionData,
      transformingDataCollector.reductionData,
      countingDataCollector.reductionData,
      parallelDataCollector.reductionData,
      profilingDataCollector.reductionData,
      deadCodeDataCollector.reductionData
    )
  }
}

