package maf.language.scheme.interpreter

import maf.core.{Identifier, Identity}
import maf.core.Position.Position
import maf.language.scheme._

import scala.concurrent.Future

object ConcreteValues:

    trait Value:
        def toDisplayedString(deref: Addr => Value): String = this.toString


    sealed trait AddrInfo:
        def idn: Identity

    trait Prim:
        val name: String

        def call(fexp: SchemeFuncall, args: List[(SchemeExp, Value)]): Value

    trait SimplePrim extends Prim:
        def call(args: List[Value], position: Position): Value

        def call(fexp: SchemeFuncall, args: List[(SchemeExp, Value)]): Value = call(args.map(_._2), fexp.idn.pos)

    type Addr = (Int, AddrInfo)
    type Env = Map[String, Addr]
    type Store = Map[Addr, Value]

    object AddrInfo:
        case class VarAddr(vrb: Identifier) extends AddrInfo:
            def idn = vrb.idn
        case class PrmAddr(nam: String) extends AddrInfo:
            def idn = Identity.none
        case class PtrAddr(exp: SchemeExp) extends AddrInfo:
            def idn = exp.idn
        case class PtrIgnoreAddr(exp: SchemeExp) extends AddrInfo:
            def idn = exp.idn

    object Value:

        /* arises from undefined behavior */
        case class Undefined(idn: Identity) extends Value:
            override def toString: String = "#<unspecified>"

        case class Clo(lambda: SchemeLambdaExp, env: Env) extends Value:
            override def toString: String = s"#<procedure:${lambda.lambdaName}>"
            override def toDisplayedString(deref: Addr => Value): String =
                // Hacky, this is to make sure we can apply a regex safely for procs containing > in their name
                s"#<procedure:${lambda.lambdaName} ()>"

        case class Primitive(p: String) extends Value:
            override def toString: String = s"#<primitive:$p>"

        case class Str(str: String) extends Value:
            override def toString: String = str
            override def toDisplayedString(deref: Addr => Value): String=
                str
                    .replaceAll("([^\\\\])\\\\n", "$1\n").nn
                    .replaceAll("^\\\\n", "\n").nn
                    .replaceAll("\\\\t", "\t").nn
                    .replaceAll("\\\\\"", "\"").nn
                    .replaceAll("\\\\\\\\", "\\\\").nn

        case class Symbol(sym: String) extends Value:
            override def toString: String = s"'$sym"
            override def toDisplayedString(deref: Addr => Value): String = sym

        case class Integer(n: BigInt) extends Value:
            override def toString: String = n.toString

        case class Real(r: Double) extends Value:
            override def toString: String = r.toString

        case class Bool(b: Boolean) extends Value:
            override def toString: String = if b then "#t" else "#f"

        case class Pointer(v: Addr) extends Value:
            override def toString: String = s"#<ptr $v>"
            override def toDisplayedString(deref: Addr => Value): String = deref(v).toDisplayedString(deref)

        case class Character(c: Char) extends Value:
            override def toString: String = c match
                case ' '  => "#\\space"
                case '\n' => "#\\newline"
                case c    => s"#\\$c"
            override def toDisplayedString(deref: Addr => Value): String = s"$c"

        case object Nil extends Value:
            override def toString: String = "'()"
            override def toDisplayedString(deref: Addr => Value): String = "()"

        case class Cons(car: Value, cdr: Value) extends Value:
            override def toString: String = s"#<cons $car $cdr>"
            override def toDisplayedString(deref: Addr => Value): String = s"(${displayAsList(deref)})"
            def displayAsList(deref: Addr => Value): String = cdr match
                case Nil => s"${car.toDisplayedString(deref)}"
                case v: Cons => s"${car.toDisplayedString(deref)} ${v.displayAsList(deref)}"
                case Pointer(addr) => deref(addr) match
                    case v: Cons => s"${car.toDisplayedString(deref)} ${v.displayAsList(deref)}"
                    case v => s"${car.toDisplayedString(deref)} . ${cdr.toDisplayedString(deref)}"
                case _ => s"${car.toDisplayedString(deref)} . ${cdr.toDisplayedString(deref)}"

        case class Vector(
            size: BigInt,
            elems: Map[BigInt, Value],
            init: Value)
            extends Value:
            override def toString: String = s"#<vector[size:$size]>"
            override def toDisplayedString(deref: Addr => Value): String =
                val content = (BigInt(0) until size).map(i => elems.get(i).getOrElse(init).toDisplayedString(deref)).mkString(" ")
                s"#($content)"

        case class InputPort(port: Handle) extends Value:
            override def toString: String = s"#<input-port:$port>"

        case class OutputPort(port: Handle) extends Value:
            override def toString: String = s"#<output-port:$port>"

        case class Thread(fut: Future[Value]) extends Value:
            override def toString: String = s"#<thread>"

        case class Lock(l: java.util.concurrent.locks.Lock) extends Value:
            override def toString: String = "#<lock>"

        case class CThread(tid: Int) extends Value:
            override def toString: String = s"#<thread:$tid>"

        case object EOF extends Value:
            override def toString: String = "#<eof>"

        case object Void extends Value:
            override def toString: String = "#<void>"
            override def toDisplayedString(deref: Addr => Value): String = s"#<unspecified>"

        /** An error as a value */
        case class Error(e: ProgramError) extends Value:
            override def toString: String = s"<#error: $e>"
