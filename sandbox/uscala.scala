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
    //final case class Macro(name: Name, typ: Type.Func, impl: Term => Term) extends Stmt
    final case class Import(sel: Select) extends Stmt
    sealed trait Term extends Stmt
      final case class Ascribe(value: Term, typ: Type) extends Term
      final case class Func(name: Name, typ: Type, value: Term) extends Term
      final case class Block(stats: List[Stmt]) extends Term
      final case class New(stats: List[Stmt]) extends Term
      final case class Apply(fun: Term, arg: Term) extends Term
      final case class Name(value: String) extends Term
      final case class Select(prefix: Term, name: Name) extends Term

object util {
  implicit def show[T <: Tree]: Show[T] = Show {
    case Val(name, typ, value)  => s("val ", name, ": ", typ, " = ", value)
    case Import(sel)            => s("import ", sel)
    case Func(name, typ, value) => s(name, ": ", typ, " => ", value)
    case Block(stats)           => s("{", r(stats, "; "), "}")
    case New(stats)             => s("new {", r(stats, "; "), "}")
    case Name(value)            => s(value)
    case Select(pre, name)      => s(pre, ".", name)
    case Apply(f, arg)          => s(f, "(", arg, ")")
  }

  def abort(msg: String): Nothing = throw new Exception(msg)
}
import util._

/*
object parse extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>")
  lexical.reserved   ++= List("new", "val", "import", "macro")

  def name:  Parser[Name]    = ident                                ^^ Name
  def block: Parser[Block]   = "{" ~> rep(term) <~ "}"              ^^ Block
  def `new`: Parser[New]     = "new" ~> "{" ~> rep(term) <~ "}"     ^^ New
  def app:   Parser[Apply]   = term ~ ("(" ~> term <~ ")")          ^^ { case f ~ arg => Apply(f, arg) }
  def sel:   Parser[Select]  = term ~ ("." ~> name)                 ^^ { case x ~ y => Select(x, y) }
  def ascr:  Parser[Ascribe] = term ~ (":" ~> typ)                  ^^ { case x ~ t => Ascribe(x, t) }
  def func:  Parser[Func]    = name ~ (":" ~> typ) ~ ("=>" ~> term) ^^ { case x ~ t ~ b => Func(x, t, b) }
  def parens: Parser[Term]   = "(" ~> term <~ ")"
  def term:  Parser[Term]    = name | block | `new` | app | sel | ascr | func | parens

  def `val`:    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term) ^^ { case x ~ t ~ b => Val(x, t, b) }
  def `import`: Parser[Import] = "import" ~> path                               ^^ Import
  def stmt:     Parser[Stmt]   = `val` | `import` | term

  def trec:  Parser[Type.Rec]  = "{" ~> rep(("val" ~> name) ~ (":" ~> typ)) <~ "}"
                                 ^^ { fields => Type.Rec(fields.map { case a ~ b => (a, b) }) }
  def typ:   Parser[Type]      = trec ~ rep("=>" ~> trec)
                                 ^^ { case first ~ rest => rest.foldRight[Type](first)(Type.Func(_, _)) }

  def path: Parser[Select] = name ~ ("." ~> name) ^^ { case x ~ y => Select(x, y) }

  def program = rep(stmt)

  def apply(s: String, parser: Parser[T} = program) = phrase(program)(new lexical.Scanner(new CharSequenceReader(s)))
}
*/

object parse extends StandardTokenParsers {
  import scala.reflect.{core => meta}
  import scala.reflect.syntactic.parsers._

  def apply(s: String): List[Stmt] = ???
}

/*
object typecheck {
  def apply(stats: List[Stmt]): List[Stmt] = ???
}

object expand {
  def apply(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats
  def apply(t: Term)(implicit env: Env = Map.empty): Term = t
}

object eval {
  type Env = Map[Name, Term]

  def apply(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats match {
    case Nil => Nil
    case (v @ Val(name, body)) :: rest =>
      val ebody = eval(body)
      Val(name, ebody) :: eval(rest)(env + (name -> ebody))
    case Import(sel @ Select(_, name)) :: rest =>
      eval(rest)(env + (name -> sel))
    case (t: Term) :: rest =>
      eval(t) :: eval(rest)
    case (m: Macro) :: rest =>
      abort(s"found non-erased macro $m")
  }

  def apply(term: Term)(implicit env: Env = Map.empty): Term = {
    val res = term match {
      case Apply(fun, value) =>
        val efun = eval(fun)
        efun match {
          case Func(name, body) => eval(body)(env + (name -> value))
          case _                => abort("can't apply $value to $efun")
        }
      case Block(stats) =>
        eval(stats) match {
          case Nil               => Block(Nil)
          case _ :+ (last: Term) => last
          case _                 => Block(Nil)
        }
      case Select(qual, name) =>
        val equal = eval(qual)
        equal match {
          case New(stats) =>
            stats collectFirst {
              case Val(vname, value) if vname == name => value
            } getOrElse {
              abort(s"object $equal doesn't have field $name")
            }
          case other =>
            abort(s"can't select $name from $equal")
        }
      case New(stats) => New(eval(stats).filter(_.isInstanceOf[Val]))
      case func: Func => func
      case name: Name => eval(env.get(name).getOrElse(abort(s"can't resolve name $name")))
    }
    println(s"eval($term) = $res")
    res
  }
}

object mscala extends App {
  def run(s: String) = eval(expand(typecheck(parse(s))))

  run("""
    val x: {} = {}
  """)
}

*/

object mscala extends App {
  println(parse("new { val x = {}}"))
}
