package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds

trait TreeTemplate {
  type C[T <: Tree]

  sealed trait Tree { override def toString = showTree(this).toString }
    sealed trait Type extends Tree
    object Type {
      final case class Func(from: C[Type], to: C[Type]) extends Type
      final case class Rec(fields: List[(C[Name], C[Type])]) extends Type
    }
    sealed trait Stmt extends Tree
      final case class Val(name: C[Name], typ: C[Type], value: C[Term]) extends Stmt
      final case class Import(t: C[Term], sels: List[C[Import.Sel]]) extends Stmt
      object Import {
        sealed trait Sel extends Tree
        final case class Rename(from: C[Name], to: C[Name]) extends Sel
        final case class Exclude(name: C[Name]) extends Sel
        final case object Wildcard extends Sel
      }
      sealed trait Term extends Stmt
        final case class Ascribe(value: C[Term], typ: C[Type]) extends Term
        final case class Func(name: C[Name], typ: C[Type], value: C[Term]) extends Term
        final case class Block(stats: List[C[Stmt]]) extends Term
        final case class New(stats: List[C[Stmt]]) extends Term
        final case class Apply(fun: C[Term], arg: C[Term]) extends Term
        final case class Name(value: String) extends Term with Import.Sel
        final case class Select(prefix: C[Term], name: C[Name]) extends Term

  implicit def showC[T <: Tree]: Show[C[T]]
  implicit def showTree[T <: Tree]: Show[T] = Show {
    case Type.Func(from, to)    => s(from, " => ", to)
    case Type.Rec(Nil)          => s("{}")
    case Type.Rec(fields)       => s("{ ", r(fields.map { case (n, t) => s("val ", n, ": ", t) }, " "), " }")
    case Val(name, typ, value)  => s("val ", name, ": ", typ, " = ", value)
    case Import(from, sels)     => s("import ", from, ".{", r(sels), "}")
    case Import.Rename(fr, to)  => s(fr, " => ", to)
    case Import.Exclude(n)      => s(n, " => _")
    case Import.Wildcard        => s("_")
    case Ascribe(term, typ)     => s(term, ": ", typ)
    case Func(name, typ, value) => s("(", name, ": ", typ, ") => ", value)
    case Block(Nil)             => s("{}")
    case Block(stats)           => s("{ ", r(stats.map(i(_)), " "), n("}"))
    case New(Nil)               => s("new {}")
    case New(stats)             => s("new { ", r(stats.map(i(_)), "; "), n("}"))
    case Name(value)            => s(value)
    case Select(pre, name)      => s(pre, ".", name)
    case Apply(f, arg)          => s(f, "(", arg, ")")
  }
}

object Untyped extends TreeTemplate {
  type C[T <: Tree] = T
  implicit def showC[T <: Tree]: Show[C[T]] = showTree
}

object Typed extends TreeTemplate {
  sealed trait C[+T <: Tree] { def tree: T; override def toString = showC[T](this).toString }
  final case class Of[T <: Term](tree: T, tpe: No[Type]) extends C[T]
  final case class No[T <: Tree](tree: T) extends C[T]

  implicit def showC[T <: Tree]: Show[C[T]] = Show {
    case Of(term, tpe) => s("<", term, "> :: ", tpe.tree)
    case No(tree)      => s(tree)
  }
}

object abort { def apply(msg: String): Nothing = throw new Exception(msg) }

object parse extends StandardTokenParsers {
  import Untyped._

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
  import uscala.{Untyped => U}
  import Typed._

  type Env = Map[Name, No[Type]]

  implicit class Subtype(me: C[Type]) {
    def `<:`(other: C[Type]): Boolean = (me.tree, other.tree) match {
      case (a, b) if a == b => true
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case (n, t) =>
          fields2.collectFirst { case (n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
    }
  }

  def sels(sels: List[U.Import.Sel])(implicit env: Env = Map.empty): List[Import.Sel] = ???

  def stats(ss: List[U.Stmt])(implicit env: Env = Map.empty): (Env, List[C[Stmt]]) = ss match {
    case Nil => (Map.empty, Nil)
    case U.Val(n: U.Name, tpt, body) :: rest =>
      val tn = Name(n.value)
      val ttpt = typ(tpt)
      val bind= tn -> ttpt
      val tbody = term(body)(env + bind)
      val (tenv, trest) = stats(rest)(env + bind)
      (tenv + bind, No(Val(No(tn), ttpt, tbody)) :: trest)
  }

  def term(tree: U.Term)(implicit env: Env = Map.empty): Of[Term] = tree match {
    case n: U.Name =>
      val tn = Name(n.value)
      if (!env.contains(tn)) abort(s"$tn is not in scope")
      else Of(tn, env(tn))

    case U.Func(x, tpt, body) =>
      val tx = Name(x.value)
      val ttpt = typ(tpt)
      val tbody = term(body)(env + (tx -> ttpt))
      Of(Func(No(tx), ttpt, tbody), No(Type.Func(ttpt, tbody.tpe)))

    case U.Apply(f, arg) =>
      val tf = term(f)
      val targ = term(arg)
      tf.tpe.tree match {
        case tpe @ Type.Func(from, to: No[Type]) =>
          if (targ.tpe `<:` from)
            Of(Apply(tf, targ), to)
          else
            abort(s"function expected $from but got ${targ.tpe}")
        case _ =>
          abort(s"one can only apply to function values")
      }

    case U.Block(blockstats) =>
      val (_, tstats) = stats(blockstats)
      val tpe: No[Type] = tstats match {
        case _ :+ (t: Of[_]) => t.tpe
        case _               => No(Type.Rec(Nil))
      }
      Of(Block(tstats), tpe)

    case U.New(newstats) =>
      val (tenv, tstats) = stats(newstats)
      val tpe = No[Type](Type.Rec(tenv.map { case (n, t) => (No(Name(n.value)), t) }.toList))
      Of(New(tstats), tpe)

    case U.Select(obj, name: U.Name) =>
      val tobj = term(obj)
      val tsel = tobj.tpe.tree match {
        case Type.Rec(fields) =>
          fields.collectFirst { case field @ (n, t: No[Type]) if n.tree.value == name.value => t }.getOrElse {
            abort(s"object doesn't have a field $name")
          }
        case _ =>
          abort(s"can't select from non-object value")
      }
      Of(Select(tobj, No(Name(name.value))), tsel)
  }

  def typ(tree: U.Type)(implicit env: Env = Map.empty): No[Type] = tree match {
    case U.Type.Func(from, to) => No(Type.Func(typ(from), typ(to)))
    // TODO: validate that there no repetion a-la { val x: {} val x: {} }
    case U.Type.Rec(fields) => No(Type.Rec(fields.map { case (U.Name(n), t) => (No(Name(n)), typ(t)) }))
  }
}

/*
object expand {
  type Env = Map[Name, Term => Term]

  var i = 0
  def fresh(pre: String = "x") = { i += 1; Name(pre + "$" + i) }

  def bstats(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats match {
    case Nil                     => Nil
    case (t: Term) :: rest       => expand(t) :: bstats(rest)
    case Val(n, t, b) :: rest    =>
      val x = fresh(n.value)
      val newenv = env + (n -> ((_: Term) => x))
      Val(x, t, expand(b)(newenv)) :: bstats(rest)(newenv)
    case Import(t, sels) :: rest => Import(expand(t), sels) :: bstats(rest) // TODO: rename this guys too
  }

  def nstats(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats.map {
    case t:        => expand(t)
    case Val(n, t, b)    => Val(n, t, expand(b))
    case Import(t, sels) => Import(expand(t), sels)
  }

  def apply(t: Term)(implicit env: Env = Map.empty): Term = t match {
    case Apply(fun, arg)    => Apply(expand(fun), expand(arg))
    case Block(stats)       => Block(expand.bstats(stats))
    case Select(qual, name) => Select(expand(qual), name)
    case Ascribe(v, t)      => Ascribe(expand(v), t)
    case New(stats)         => New(expand.nstats(stats))
    case Func(n, t, b)      => val x = fresh(n.value); Func(x, t, expand(b)(env + (n -> (_ => x))))
    case n: Name            => env.get(n).map(f => f(n)).getOrElse(n)
  }
}

object eval {
  type Env = Map[Name, Term]

  var steps = 0
  val limit = 100

  def addb(env: Env, binding: (Name, Term)): Env = {
    val (n, _) = binding
    if(env.contains(n)) println(s"!!!!!!! entered $n twice")
    env + binding
  }

  def addbs(env: Env, bindings: List[(Name, Term)]): Env = {
    var env1 = env
    bindings.foreach { b => env1 = addb(env1, b) }
    env1
  }

  def stats(stats: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = stats match {
    case Nil => Nil
    case (v @ Val(name, tpt, body)) :: rest =>
      val ebody = eval(body)(addb(env, name -> body))
      Val(name, tpt, ebody) :: eval.stats(rest)(addb(env, name -> ebody))
    case Import(t, sels) :: rest =>
      val bindings = sels.map {
        case n: Name                 => n -> Select(t, n)
        case Import.Rename(from, to) => to -> Select(t, from)
        case _                       => ???
      }
      eval.stats(rest)(addbs(env, bindings))
    case (t: Term) :: rest =>
      eval(t) :: eval.stats(rest)
  }

  def apply(term: Term)(implicit env: Env = Map.empty): Term = {
    steps += 1
    if (steps > limit) abort("step limit reached")
    val res = term match {
      case Apply(fun, value) =>
        val efun = eval(fun)
        efun match {
          case Func(name, _, body) => eval(body)(addb(env, name -> value))
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
}*/

object Test extends App {
  val parsed = parse("((x: {}) => x)(new { val x: {} = {} })")
  println(parsed)
  //eval.stats(parsed.get)
  //val exp = expand.nstats(parsed.get)
  //println(s"expanded: $exp")
  //eval.stats(exp)
  val typechecked = typecheck.term(parsed.get.head.asInstanceOf[Untyped.Term])
  println(s"typechecked: $typechecked")
}
