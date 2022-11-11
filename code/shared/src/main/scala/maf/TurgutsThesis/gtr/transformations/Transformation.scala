package maf.TurgutsThesis.gtr.transformations

import maf.language.scheme.SchemeExp

abstract class Transformation:
  var trees: List[SchemeExp] = List()
  var replacements: List[SchemeExp] = List()

  def addTree(t: SchemeExp): Unit =
    trees = trees.::(t)
    
  def addTrees(ts: List[SchemeExp]): Unit =
    ts.foreach(addTree)

  def addReplacement(replacement: SchemeExp): Unit =
    replacements = replacements.::(replacement)
    
  def addReplacements(rs: List[SchemeExp]): Unit =
    rs.foreach(addReplacement)

  /** Template method transform definition */
  def transform(tree: SchemeExp, node: SchemeExp): List[SchemeExp] =
    require(tree.contains(node))
    trees = List()
    replacements = List()

    transformAndAdd(tree, node) //should fill trees and replacements

    (trees ++ replacements.map(r => tree.replace(node, r)))
      .filterNot(newTree => tree eql newTree) //if a transformation suggest a tree that is eql to the current tree, discard that suggestions

  /** transformAndAdd is a subclass responsibility */
  def transformAndAdd(tree: SchemeExp, node: SchemeExp): Unit

  val name: String
  private var hits: Int = 0
  def getHits: Int = hits
  def hit(tree: SchemeExp, idx: Int): Unit =
    hits += 1