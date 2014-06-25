package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds

trait TreeTemplate {
  type BindMeta
  type TermMeta
  type TypeMeta

  def emptyBindMeta: BindMeta
  def emptyTermMeta: TermMeta
  def emptyTypeMeta: TypeMeta

  sealed trait Tree { override def toString = showTree(this).toString }
    case class Name(value: String) extends Tree with Import.Sel
    case class Bind(name: Name, typ: Type, meta: BindMeta = emptyBindMeta) extends Tree
    sealed trait Type extends Tree { def meta: TypeMeta }
    object Type {
      case class Func(from: Type, to: Type, meta: TypeMeta = emptyTypeMeta) extends Type
      case class Rec(fields: List[Bind], meta: TypeMeta = emptyTypeMeta) extends Type
    }
    sealed trait Stmt extends Tree
      case class Val(bind: Bind, value: Term) extends Stmt
      case class Import(t: Term, sels: List[Import.Sel]) extends Stmt
      object Import {
        sealed trait Sel extends Tree
        case class Rename(from: Name, to: Name) extends Sel
        case class Exclude(name: Name) extends Sel
        case object Wildcard extends Sel
      }
      sealed trait Term extends Stmt { def meta: TermMeta }
        case class Ascribe(value: Term, typ: Type, meta: TermMeta = emptyTermMeta) extends Term
        case class Func(bind: Bind, value: Term, meta: TermMeta = emptyTermMeta) extends Term
        case class Block(stats: List[Stmt], meta: TermMeta = emptyTermMeta) extends Term
        case class New(stats: List[Stmt], meta: TermMeta = emptyTermMeta) extends Term
        case class Apply(fun: Term, arg: Term, meta: TermMeta = emptyTermMeta) extends Term
        case class Select(prefix: Term, name: Name, meta: TermMeta = emptyTermMeta) extends Term
        case class Ident(name: Name, meta: TermMeta = emptyTermMeta) extends Term

  implicit def showTree[T <: Tree]: Show[T] = Show {
    case Type.Func(from, to, _) => s(from, " => ", to)
    case Type.Rec(Nil, _)       => s("{}")
    case Type.Rec(fields, _)    => s("{ ", r(fields.map { b => s("val ", b) }, " "), " }")
    case Val(bind, value)       => s("val ", bind, " = ", value)
    case Import(from, sels)     => s("import ", from, ".{", r(sels), "}")
    case Import.Rename(fr, to)  => s(fr, " => ", to)
    case Import.Exclude(n)      => s(n, " => _")
    case Import.Wildcard        => s("_")
    case Ascribe(term, typ, _)  => s(term, ": ", typ)
    case Func(bind, value, _)   => s("(", bind, ") => ", value)
    case Block(Nil, _)          => s("{}")
    case Block(stats, _)        => s("{ ", r(stats.map(i(_)), " "), n("}"))
    case New(Nil, _)            => s("new {}")
    case New(stats, _)          => s("new { ", r(stats.map(i(_)), "; "), n("}"))
    case Name(value)            => s(value)
    case Ident(name, _)         => s(name)
    case Select(pre, name, _)   => s(pre, ".", name)
    case Apply(f, arg, _)       => s(f, "(", arg, ")")
    case Bind(n, t, _)          => s(n, ": ", t)
  }
}

object Untyped extends TreeTemplate {
  type BindMeta = Null
  type TermMeta = Null
  type TypeMeta = Null

  def emptyBindMeta: BindMeta = null
  def emptyTermMeta: TermMeta = null
  def emptyTypeMeta: TypeMeta = null
}

object Typed extends TreeTemplate {
  type BindMeta = Null
  type TermMeta = Type
  type TypeMeta = Null

  def emptyBindMeta: BindMeta = null
  def emptyTermMeta: TermMeta = abort("typed terms must contain a type")
  def emptyTypeMeta: TypeMeta = null

  override implicit def showTree[T <: Tree]: Show[T] = Show {
    case t: Term => s("<", super.showTree(t), "> :: ", t.meta)
    case t       => super.showTree(t)
  }
}

object abort { def apply(msg: String): Nothing = throw new Exception(msg) }

object parse extends StandardTokenParsers {
  import Untyped._

  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>", ".", "=", ",", ";")
  lexical.reserved   ++= List("new", "val", "import", "macro", "_")

  def name:   Parser[Name]  = ident                                ^^ { s => Name(s) }
  def id:     Parser[Ident] = name                                 ^^ { n => Ident(n) }
  def block:  Parser[Block] = "{" ~> rep(stmt) <~ "}"              ^^ { stats => Block(stats) }
  def `new`:  Parser[New]   = "new" ~> "{" ~> rep(stmt) <~ "}"     ^^ { stats => New(stats) }
  def func:   Parser[Func]  = ("(" ~> name ~ (":" ~> typ) <~ ")") ~ ("=>" ~> term) ^^ { case x ~ t ~ b => Func(Bind(x, t), b) }
  def parens: Parser[Term]  = "(" ~> term <~ ")"
  def term1:  Parser[Term]  = id | block | `new` | func | parens
  def term2:  Parser[Term]  = term1 ~ opt("." ~> name)             ^^ { case x ~ y => (x /: y)(Select(_, _)) }
  def term3:  Parser[Term]  = term2 ~ opt("(" ~> term <~ ")")      ^^ { case x ~ y => (x /: y)(Apply(_, _)) }
  def term:   Parser[Term]  = term3 ~ opt(":" ~> typ)              ^^ { case x ~ t => (x /: t)(Ascribe(_, _)) }

  def nameOrWildcard: Parser[Name => Import.Sel] = (name ^^ ((y: Name) => (x: Name) => Import.Rename(y, x))) |
                                                   ("_" ^^^ ((x: Name) => Import.Exclude(x)))
  def sel: Parser[Import.Sel]  = (name ~ opt("=>" ~> nameOrWildcard)  ^^
                                  { case x ~ fopt => fopt.map(f => f(x)).getOrElse(x) }) |
                                 ("_" ^^^ Import.Wildcard)
  def `import`: Parser[Import] = "import" ~> term ~ ("." ~> "{" ~> repsep(sel, ",") <~ "}") ^^ { case from ~ sels => Import(from, sels) }

  def `val`:    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term) ^^ { case x ~ t ~ b => Val(Bind(x, t), b) }
  def stmt:     Parser[Stmt]   = `val` | `import` | term

  def trec:  Parser[Type.Rec]  = "{" ~> rep(("val" ~> name) ~ (":" ~> typ)) <~ "}" ^^ {
    fields => Type.Rec(fields.map { case a ~ b => Bind(a, b) })
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

  type Env = Map[String, Type]

  implicit class Subtype(me: Type) {
    def `<:`(other: Type): Boolean = (me, other) match {
      case (a, b) if a == b => true
      case (Type.Func(s1, s2, _), Type.Func(t1, t2, _)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1, _), Type.Rec(fields2, _)) =>
        fields1.forall { case Bind(n, t, _) =>
          fields2.collectFirst { case Bind(n2, t2, _) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
    }
  }

  def sels(sels: List[U.Import.Sel])(implicit env: Env = Map.empty): List[Import.Sel] = ???

  def stats(ss: List[U.Stmt])(implicit env: Env = Map.empty): (Env, List[Stmt]) = ss match {
    case Nil => (Map.empty, Nil)

    case U.Val(U.Bind(n: U.Name, tpt, _), body) :: rest =>
      val tn = Name(n.value)
      val ttpt = typ(tpt)
      val bind= tn.value -> ttpt
      val tbody = term(body)(env + bind)
      val (tenv, trest) = stats(rest)(env + bind)
      (tenv + bind, Val(Bind(tn, ttpt), tbody) :: trest)

    case U.Import(t, sels) :: rest =>
      val tt = term(t)
      val sels = ???
      val (tenv, trest) = stats(rest)
      (tenv, Import(tt, sels) :: trest)

    case (t: U.Term) :: rest =>
      val tt = term(t)
      val (tenv, trest) = stats(rest)
      (tenv, tt :: trest)
  }

  def term(tree: U.Term)(implicit env: Env = Map.empty): Term = tree match {
    case U.Ident(n: U.Name, _)=>
      if (!env.contains(n.value)) abort(s"$n is not in scope")
      else Ident(Name(n.value), env(n.value))

    case U.Func(U.Bind(x, tpt, _), body, _) =>
      val tx = Name(x.value)
      val ttpt = typ(tpt)
      val tbody = term(body)(env + (tx.value -> ttpt))
      Func(Bind(tx, ttpt), tbody, Type.Func(ttpt, tbody.meta))

    case U.Apply(f, arg, _) =>
      val tf = term(f)
      val targ = term(arg)
      tf.meta match {
        case tpe @ Type.Func(from, to, _) =>
          if (targ.meta `<:` from)
            Apply(tf, targ, to)
          else
            abort(s"function expected $from but got ${targ.meta}")
        case _ =>
          abort(s"one can only apply to function values")
      }

    case U.Block(blockstats, _) =>
      val (_, tstats) = stats(blockstats)
      val tpe: Type = tstats match {
        case _ :+ (t: Term) => t.meta
        case _              => Type.Rec(Nil)
      }
      Block(tstats, tpe)

    case U.New(newstats, _) =>
      val (tenv, tstats) = stats(newstats)
      val tpe = Type.Rec(tenv.map { case (n, t) => Bind(Name(n), t) }.toList)
      New(tstats, tpe)

    case U.Select(obj, name: U.Name, _) =>
      val tobj = term(obj)
      val tsel = tobj.meta match {
        case Type.Rec(fields, _) =>
          fields.collectFirst { case field @ Bind(n, t, _) if n.value == name.value => t }.getOrElse {
            abort(s"object doesn't have a field $name")
          }
        case _ =>
          abort(s"can't select from non-object value")
      }
      Select(tobj, Name(name.value), tsel)

    case U.Ascribe(t, tpt, _) =>
      ???
  }

  def typ(tree: U.Type)(implicit env: Env = Map.empty): Type = tree match {
    case U.Type.Func(from, to, _) => Type.Func(typ(from), typ(to))
    // TODO: validate that there no repetion a-la { val x: {} val x: {} }
    case U.Type.Rec(fields, _) => Type.Rec(fields.map { case U.Bind(U.Name(n), t, _) => Bind(Name(n), typ(t)) })
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
