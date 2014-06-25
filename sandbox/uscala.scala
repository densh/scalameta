package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds

trait TreeTemplate {
  type TermInfo
  type NameInfo

  def emptyTermInfo: TermInfo
  def emptyNameInfo: NameInfo

  sealed trait Tree { override def toString = showTree(this).toString }
    case class Bind(name: Name, typ: Type) extends Tree
    sealed trait Type extends Tree
    object Type {
      case class Func(from: Type, to: Type) extends Type
      case class Rec(fields: List[Bind]) extends Type
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
      sealed trait Term extends Stmt { def tpe: TermInfo }
        case class Ascribe(value: Term, typ: Type, tpe: TermInfo = emptyTermInfo) extends Term
        case class Func(bind: Bind, value: Term, tpe: TermInfo = emptyTermInfo) extends Term
        case class Block(stats: List[Stmt], tpe: TermInfo = emptyTermInfo) extends Term
        case class New(stats: List[Stmt], tpe: TermInfo = emptyTermInfo) extends Term
        case class Apply(fun: Term, arg: Term, tpe: TermInfo = emptyTermInfo) extends Term
        case class Select(prefix: Term, name: Name, tpe: TermInfo = emptyTermInfo) extends Term
        case class Name(value: String, tpe: TermInfo = emptyTermInfo,
                        lex: NameInfo = emptyNameInfo) extends Term with Import.Sel

  implicit def showTree[T <: Tree]: Show[T] = Show {
    case Type.Func(from, to)    => s(from, " => ", to)
    case Type.Rec(Nil)          => s("{}")
    case Type.Rec(fields)       => s("{ ", r(fields.map { b => s("val ", b) }, " "), " }")
    case Val(bind, value)       => s("val ", bind, " = ", value)
    case Import(from, sels)     => s("import ", from, ".{", r(sels, ", "), "}")
    case Import.Rename(fr, to)  => s(fr, " => ", to)
    case Import.Exclude(n)      => s(n, " => _")
    case Import.Wildcard        => s("_")
    case Ascribe(term, typ, _)  => s(term, ": ", typ)
    case Func(bind, value, _)   => s("(", bind, ") => ", value)
    case Block(Nil, _)          => s("{}")
    case Block(stats, _)        => s("{ ", r(stats.map(i(_)), " "), n("}"))
    case New(Nil, _)            => s("new {}")
    case New(stats, _)          => s("new { ", r(stats.map(i(_))), n("}"))
    case n: Name                => s(n.value)
    case Select(pre, name, _)   => s(pre, ".", name)
    case Apply(f, arg, _)       => s(f, "(", arg, ")")
    case Bind(n, t)             => s(n, ": ", t)
  }
}

object Untyped extends TreeTemplate {
  type TermInfo = Null
  type NameInfo = Null
  def emptyTermInfo: TermInfo = null
  def emptyNameInfo: NameInfo = null
}

object Typed extends TreeTemplate {
  type TermInfo = Type
  type NameInfo = Null
  def emptyTermInfo: TermInfo = null
  def emptyNameInfo: NameInfo = null

  override implicit def showTree[T <: Tree]: Show[T] = Show {
    case t: Term if t.tpe != null => s("<", super.showTree(t), "> :: ", t.tpe)
    case t                         => super.showTree(t)
  }
}

object Expanded extends TreeTemplate {
  case class Lex(id: Int)

  type TermInfo = Type
  type NameInfo = Lex
  def emptyTermInfo: TermInfo = null
  def emptyNameInfo: NameInfo = null

  override implicit def showTree[T <: Tree]: Show[T] = Show {
    case t: Name                  => s(super.showTree(t),
                                       if (t.lex != null) s("#", t.lex.id.toString) else s(),
                                       if (t.tpe != null) s(" :: ", t.tpe) else s())
    case t: Term if t.tpe != null => s("<", super.showTree(t), "> :: ", t.tpe)
    case t                        => super.showTree(t)
  }
}

object abort { def apply(msg: String): Nothing = throw new Exception(msg) }

object parse extends StandardTokenParsers {
  import Untyped._

  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>", ".", "=", ",", ";")
  lexical.reserved   ++= List("new", "val", "import", "macro", "_")

  def name:   Parser[Name]  = ident                                ^^ { s => Name(s) }
  def block:  Parser[Block] = "{" ~> rep(stmt) <~ "}"              ^^ { stats => Block(stats) }
  def `new`:  Parser[New]   = "new" ~> "{" ~> rep(stmt) <~ "}"     ^^ { stats => New(stats) }
  def func:   Parser[Func]  = ("(" ~> name ~ (":" ~> typ) <~ ")") ~ ("=>" ~> term) ^^ { case x ~ t ~ b => Func(Bind(x, t), b) }
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
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case Bind(n, t) =>
          fields2.collectFirst { case Bind(n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
    }
  }

  def imp(t: Term, sels: List[Import.Sel])(implicit env: Env = Map.empty): List[(String, Type)] = {
    import Import._
    val (wildcards, nonwild) = sels.span(_ == Wildcard)
    val (exclusions, nonexcluded) = nonwild.span(_.isInstanceOf[Exclude])
    val members: Map[Name, Type] = t.tpe match {
      case Type.Func(_, _)  => Map.empty
      case Type.Rec(fields) => fields.map { case Bind(n, t) => (n, t) }.toMap
    }
    def getmember(n: Name): Type = {
      val opt: Option[Type] = members.get(n)
      opt.getOrElse { abort(s"can't import $n as it's not defined in $t") }
    }
    wildcards match {
      case Nil =>
        if (exclusions.nonEmpty) abort("can't exclude without a wildcard")
        nonexcluded map {
          case n: Name          => n.value  -> getmember(n)
          case Rename(from, to) => to.value -> getmember(from)
        }
      case _ :: Nil =>
        def loop(m: Map[Name, Type], ops: List[Sel]): Map[Name, Type] = ops match {
          case Nil                      => m
          case (n: Name) :: rest        => getmember(n); loop(m, rest)
          case Rename(from, to) :: rest => val tpe = getmember(from); loop(m - from + (to -> tpe), rest)
          case Exclude(n) :: rest       => getmember(n); loop(m - n, rest)
        }
        loop(members, nonwild).map {
          case (n: Name, t) => (n.value, t)
        }.toList
      case _ :: _ :: _  =>
        abort("can't have more than one wildcard")
    }
  }

  def stats(ss: List[U.Stmt])(implicit env: Env = Map.empty): (Env, List[Stmt]) = ss match {
    case Nil => (Map.empty, Nil)
    case U.Val(U.Bind(n: U.Name, tpt), body) :: rest =>
      val tn = Name(n.value)
      val ttpt = typ(tpt)
      val bind= tn.value -> ttpt
      val tbody = term(body)(env + bind)
      val (tenv, trest) = stats(rest)(env + bind)
      (tenv + bind, Val(Bind(tn, ttpt), tbody) :: trest)
    case U.Import(t, sels) :: rest =>
      val tt = term(t)
      // TODO: validate selectors
      val tsels = this.sels(sels)
      val binds = imp(tt, tsels)
      val (tenv, trest) = stats(rest)(env ++ binds)
      (tenv, Import(tt, tsels) :: trest)
    case (t: U.Term) :: rest =>
      val tt = term(t)
      val (tenv, trest) = stats(rest)
      (tenv, tt :: trest)
  }

  def sels(sels: List[U.Import.Sel]): List[Import.Sel] = sels map {
    case n: U.Name => Name(n.value)
    case U.Import.Rename(from: U.Name, to: U.Name) => Import.Rename(Name(from.value), Name(to.value))
    case U.Import.Exclude(n: U.Name) => Import.Exclude(Name(n.value))
    case U.Import.Wildcard => Import.Wildcard
  }

  def term(tree: U.Term)(implicit env: Env = Map.empty): Term = tree match {
    case n: U.Name =>
      if (!env.contains(n.value)) abort(s"$n is not in scope")
      else Name(n.value, env(n.value))

    case U.Func(U.Bind(x, tpt), body, _) =>
      val tx = Name(x.value)
      val ttpt = typ(tpt)
      val tbody = term(body)(env + (tx.value -> ttpt))
      Func(Bind(tx, ttpt), tbody, Type.Func(ttpt, tbody.tpe))

    case U.Apply(f, arg, _) =>
      val tf = term(f)
      val targ = term(arg)
      tf.tpe match {
        case tpe @ Type.Func(from, to) =>
          if (targ.tpe `<:` from)
            Apply(tf, targ, to)
          else
            abort(s"function expected $from but got ${targ.tpe}")
        case _ =>
          abort(s"one can only apply to function values")
      }

    case U.Block(blockstats, _) =>
      val (_, tstats) = stats(blockstats)
      val tpe: Type = tstats match {
        case _ :+ (t: Term) => t.tpe
        case _              => Type.Rec(Nil)
      }
      Block(tstats, tpe)

    case U.New(newstats, _) =>
      val (tenv, tstats) = stats(newstats)
      val tpe = Type.Rec(tenv.map { case (n, t) => Bind(Name(n), t) }.toList)
      New(tstats, tpe)

    case U.Select(obj, name: U.Name, _) =>
      val tobj = term(obj)
      val tsel = tobj.tpe match {
        case Type.Rec(fields) =>
          fields.collectFirst { case field @ Bind(n, t) if n.value == name.value => t }.getOrElse {
            abort(s"object doesn't have a field $name")
          }
        case _ =>
          abort(s"can't select from non-object value")
      }
      Select(tobj, Name(name.value), tsel)

    case U.Ascribe(t, tpt, _) =>
      val tt = term(t)
      val ttpt = typ(tpt)
      if (tt.tpe `<:` ttpt) Ascribe(tt, ttpt, ttpt)
      else abort("ascripted value isn't a proper supertype")
  }

  def typ(tree: U.Type)(implicit env: Env = Map.empty): Type = tree match {
    case U.Type.Func(from, to) => Type.Func(typ(from), typ(to))
    // TODO: validate that there no repetion a-la { val x: {} val x: {} }
    case U.Type.Rec(fields) => Type.Rec(fields.map { case U.Bind(n: U.Name, t) => Bind(Name(n.value), typ(t)) })
  }
}

object expand {
  import uscala.{Typed => T}
  import Expanded._

  type Env = Map[String, Term => Term]

  var i = 0

  def rename(n: T.Name): Name = {
    i += 1
    val tpe = if (n.tpe == null) null else typ(n.tpe)
    Name(n.value, tpe, lex = Lex(i))
  }

  def rename1(n: Name): Name = {
    i += 1
    Name(n.value, n.tpe, lex = Lex(i))
  }

  def subs(k: String, x: Name): (String, Term => Term) = k -> { t => x.copy(tpe = t.tpe) }

  def imp(t: Term, sels: List[Import.Sel])(implicit env: Env = Map.empty): (List[Import.Rename], Env) = {
    import Import._
    val (wildcards, nonwild) = sels.span(_ == Wildcard)
    val (exclusions, nonexcluded) = nonwild.span(_.isInstanceOf[Exclude])
    val members: Map[Name, Type] = t.tpe match {
      case Type.Func(_, _)  => Map.empty
      case Type.Rec(fields) => fields.map { case Bind(n, t) => (n, t) }.toMap
    }
    def getmember(n: Name): Type = members(n)
    val original = wildcards match {
      case Nil =>
        nonexcluded map {
          case n: Name          => Rename(n,    n)
          case Rename(from, to) => Rename(from, to)
        }
      case _ :: Nil =>
        def loop(m: Map[Name, Name], ops: List[Sel]): Map[Name, Name] = ops match {
          case Nil                      => m
          case (n: Name) :: rest        => getmember(n); loop(m, rest)
          case Rename(from, to) :: rest => val tpe = getmember(from); loop(m - from + (from -> to), rest)
          case Exclude(n) :: rest       => getmember(n); loop(m - n, rest)
        }
        loop(members.map { case (n, _) => n -> n }, nonwild).toList.map { case (f, t) => Rename(f, t) }
    }
    val transforms = new scala.collection.mutable.ListBuffer[(String, Term => Term)]
    (original.map {
      case Rename(from, to) =>
        val x = rename1(to)
        transforms += subs(to.value, x)
        Rename(from, x)
    }, transforms.toMap)
  }

  def stats(trees: List[T.Stmt])(implicit env: Env = Map.empty): List[Stmt] = trees match {
    case Nil                       => Nil
    case (t: T.Term) :: rest       => term(t) :: stats(rest)
    case T.Val(T.Bind(n, t), b) :: rest    =>
      val x = rename(n)
      val newenv = env + subs(n.value, x)
      Val(Bind(x, typ(t)), term(b)(newenv)) :: stats(rest)(newenv)
    case T.Import(t, sels) :: rest =>
      val et = term(t)
      val esels = this.sels(sels)
      val (renames, envupd) = imp(et, esels)
      Import(et, renames) :: stats(rest)(env ++ envupd) // TODO: rename this guys too
  }

  def term(tree: T.Term)(implicit env: Env = Map.empty): Term = tree match {
    case T.Apply(fun, arg, tpe)       => Apply(term(fun), term(arg), tpe = typ(tpe))
    case T.Block(stats, tpe)          => Block(this.stats(stats), tpe = typ(tpe))
    case T.Select(qual, name, tpe)    => Select(term(qual), Name(name.value), tpe = typ(tpe))
    case T.Ascribe(v, t, tpe)         => Ascribe(term(v), typ(t), tpe = typ(tpe))
    case T.New(stats, tpe)            => New(this.stats(stats), tpe = typ(tpe))
    case T.Func(T.Bind(n, t), b, tpe) =>
      val x = rename(n)
      Func(Bind(x, typ(t)), term(b)(env + subs(n.value, x)), tpe = typ(tpe))
    case n: T.Name                  =>
      env.get(n.value).map { f =>
        val res = f(Name(n.value, tpe = typ(n.tpe)))
        res
      }.getOrElse(abort(s"panic, can't resolve $n"))
  }

  def typ(tree: T.Type)(implicit env: Env = Map.empty): Type = tree match {
    case T.Type.Func(from, to) => Type.Func(typ(from), typ(to))
    case T.Type.Rec(fields)    => Type.Rec(fields.map { case T.Bind(n: T.Name, t) => Bind(Name(n.value), typ(t)) })
  }

  def sels(sels: List[T.Import.Sel]): List[Import.Sel] = sels map {
    case n: T.Name => Name(n.value)
    case T.Import.Rename(from: T.Name, to: T.Name) => Import.Rename(Name(from.value), Name(to.value))
    case T.Import.Exclude(n: T.Name) => Import.Exclude(Name(n.value))
    case T.Import.Wildcard => Import.Wildcard
  }
}

/*
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
}
*/

object Test extends App {
  val parsed = parse("""{
    val x: { val a: {} val b: {} } = new { val a: {} = {} val b: {} = {} }
    import x.{_}
    a
  }""")
  println(parsed)
  //eval.stats(parsed.get)
  //val exp = expand.nstats(parsed.get)
  //println(s"expanded: $exp")
  //eval.stats(exp)
  val (_, tstats) = typecheck.stats(parsed.get)
  println(s"typechecked: $tstats")
  val estats = expand.stats(tstats)
  println(s"expanded: $estats")
}
