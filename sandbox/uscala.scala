import org.scalareflect.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader

sealed trait Tree { override def toString = util.show(this).toString }
  sealed trait Type extends Tree
  object Type {
    final case class Func(from: Type, to: Type) extends Type
    final case class Rec(fields: List[(Name, Type)]) extends Type
  }
  sealed trait Stmt extends Tree
    final case class Val(name: Name, typ: Type, value: Term) extends Stmt
    final case class Import(t: Term, sels: List[Import.Sel]) extends Stmt
    object Import {
      sealed trait Sel extends Tree
      final case class Rename(from: Name, to: Name) extends Sel
      final case class Exclude(name: Name) extends Sel
      final case object Wildcard extends Sel
    }
    sealed trait Term extends Stmt
      final case class Ascribe(value: Term, typ: Type) extends Term
      final case class Func(name: Name, typ: Type, value: Term) extends Term
      final case class Block(stats: List[Stmt]) extends Term
      final case class New(stats: List[Stmt]) extends Term
      final case class Apply(fun: Term, arg: Term) extends Term
      final case class Name(value: String) extends Term with Import.Sel
      final case class Select(prefix: Term, name: Name) extends Term

object util {
  implicit def show[T <: Tree]: Show[T] = Show {
    case Type.Func(from, to)    => s(from, " => ", to)
    case Type.Rec(Nil)          => s("{}")
    case Type.Rec(fields)       => s("{ ", r(fields.map { case (n, t) => s("val ", n, ": ", t) }, " "), " }")
    case Val(name, typ, value)  => s("val ", name, ": ", typ, " = ", value)
    case Import(from, sels)     => s("import ", from, ".{", r(sels), "}")
    case Import.Rename(fr, to)  => s(fr, " => ", to)
    case Import.Exclude(n)      => s(n, " => _")
    case Import.Wildcard        => s("_")
    case Func(name, typ, value) => s(name, ": ", typ, " => ", value)
    case Block(Nil)             => s("{}")
    case Block(stats)           => s("{ ", r(stats.map(i(_)), " "), n("}"))
    case New(Nil)               => s("new {}")
    case New(stats)             => s("new { ", r(stats.map(i(_)), "; "), n("}"))
    case Name(value)            => s(value)
    case Select(pre, name)      => s(pre, ".", name)
    case Apply(f, arg)          => s(f, "(", arg, ")")
    case Ascribe(term, typ)     => s(term, ": ", typ)
  }

  def abort(msg: String): Nothing = throw new Exception(msg)
}
import util._

object parse extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>", ".", "=", ",", ";")
  lexical.reserved   ++= List("new", "val", "import", "macro", "_")

  def name:   Parser[Name]  = ident                                ^^ Name
  def block:  Parser[Block] = "{" ~> rep(stmt) <~ "}"              ^^ Block
  def `new`:  Parser[New]   = "new" ~> "{" ~> rep(stmt) <~ "}"     ^^ New
  def func:   Parser[Func]  = ("(" ~> name ~ (":" ~> typ) <~ ")") ~ ("=>" ~> term) ^^ { case x ~ t ~ b => Func(x, t, b) }
  def parens: Parser[Term]  = "(" ~> term <~ ")"
  def term1:  Parser[Term]  = name | block | `new` | func | parens
  def term2:  Parser[Term]  = term1 ~ opt("." ~> name)             ^^ { case x ~ y => (x /: y)(Select(_, _)) }
  def term3:  Parser[Term]  = term2 ~ opt("(" ~> term <~ ")")      ^^ { case x ~ y => (x /: y)(Apply(_, _)) }
  def term:   Parser[Term]  = term3 ~ opt(":" ~> typ)              ^^ { case x ~ t => (x /: t)(Ascribe(_, _)) }


  def nameOrWildcard: Parser[Name => Import.Sel] = (name ^^ ((y: Name) => (x: Name) => Import.Rename(y, x))) |
                                                   ("_" ^^^ ((x: Name) => Import.Exclude(x)))
  def sel: Parser[Import.Sel]  = (name ~ opt("=>" ~> nameOrWildcard)  ^^
                                  { case x ~ fopt => fopt.map(f => f(x)).getOrElse(x) }) |
                                 ("_" ^^^ Import.Wildcard)
  def `import`: Parser[Import] = "import" ~> term ~ ("." ~> "{" ~> repsep(sel, ",") <~ "}") ^^ { case from ~ sels => Import(from, sels) }

  def `val`:    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term) ^^ { case x ~ t ~ b => Val(x, t, b) }
  def stmt:     Parser[Stmt]   = `val` | `import` | term

  def trec:  Parser[Type.Rec]  = "{" ~> rep(("val" ~> name) ~ (":" ~> typ)) <~ "}" ^^ {
    fields => Type.Rec(fields.map { case a ~ b => (a, b) })
  }
  def typ:   Parser[Type]      = trec ~ rep("=>" ~> trec) ^^ {
    case first ~ rest => rest.foldRight[Type](first)(Type.Func(_, _))
  }

  def program = rep(stmt)

  def as[T](parser: Parser[T])(s: String): ParseResult[T] = phrase(parser)(new lexical.Scanner(new CharSequenceReader(s)))
  def apply(s: String): ParseResult[List[Stmt]] = as(program)(s)
}

object typecheck {
  def apply(stats: List[Stmt]): List[Stmt] = ???
}

object expand {
  type Env = Map[Name, Term => Term]

  def stats(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats
  def apply(t: Term)(implicit env: Env = Map.empty): Term = t
}

object eval {
  type Env = Map[Name, Term]

  def stats(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats match {
    case Nil => Nil
    case (v @ Val(name, tpt, body)) :: rest =>
      val ebody = eval(body)
      Val(name, tpt, ebody) :: eval.stats(rest)(env + (name -> ebody))
    case Import(t, sels) :: rest =>
      val bindings = sels.map {
        case n: Name                 => n -> Select(t, n)
        case Import.Rename(from, to) => to -> Select(t, from)
        case _                       => ???
      }
      eval.stats(rest)(env ++ bindings)
    case (t: Term) :: rest =>
      eval(t) :: eval.stats(rest)
  }

  def apply(term: Term)(implicit env: Env = Map.empty): Term = {
    val res = term match {
      case Apply(fun, value) =>
        val efun = eval(fun)
        efun match {
          case Func(name, _, body) => eval(body)(env + (name -> value))
          case _                   => abort("can't apply $value to $efun")
        }
      case Block(stats) =>
        eval.stats(stats) match {
          case Nil               => Block(Nil)
          case _ :+ (last: Term) => last
          case _                 => Block(Nil)
        }
      case Select(qual, name) =>
        val equal = eval(qual)
        equal match {
          case New(stats) =>
            stats collectFirst {
              case Val(vname, _, value) if vname == name => value
            } getOrElse {
              abort(s"object $equal doesn't have field $name")
            }
          case other =>
            abort(s"can't select $name from $equal")
        }
      case Ascribe(t, _) => eval(t)
      case New(stats) => New(eval.stats(stats).filter(_.isInstanceOf[Val]))
      case func: Func => func
      case name: Name => eval(env.get(name).getOrElse(abort(s"can't resolve name $name")))
    }
    println(s"eval($term) = $res")
    res
  }
}

object Test extends App {
  eval.stats(parse("""
    (new { val x: {} = {} }).x
  """).get)
}
