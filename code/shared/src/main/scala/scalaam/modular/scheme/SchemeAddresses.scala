package scalaam.modular.scheme

import scalaam.core._
import scalaam.language.scheme._

trait SchemeAddr extends Address                  
case class VarAddr(id: Identifier)  extends SchemeAddr  { def printable = true;  def idn: Identity =  id.idn }
case class PtrAddr(exp: SchemeExp)  extends SchemeAddr  { def printable = false; def idn: Identity =  exp.idn }
case class PrmAddr(nam: String)     extends SchemeAddr  { def printable = true;  def idn: Identity =  Identity.none }
