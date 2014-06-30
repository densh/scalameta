package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds


final case class Lex(id: Int = 0, marks: Set[Int] = Set.empty)
object Lex {
  val empty = Lex()

  implicit val show: Show[Lex] = Show {
    case Lex(id, marks) =>
      val base = if (id != 0) s("#", id.toString) else s()
      marks.foldRight(base) { case (m, x) => s(x, "^", m.toString) }
  }
}

sealed trait Tree { override def toString = Tree.show(this).toString }
object Tree {
  case class Name(value: String, lex: Lex = Lex.empty) extends Sel
  object Name { implicit val show: Show[Name] = Show { n => s(n.value, n.lex) } }

  sealed trait Type extends Tree
  object Type {
    case class Func(from: Type, to: Type) extends Type
    case class Rec(fields: Map[String, Type]) extends Type
    object Rec { val empty = Rec(Map.empty) }
    case object Bool extends Type
    case object Nothing extends Type

    implicit def show[T <: Type]: Show[T] = Show {
      case Type.Bool           => s("Bool")
      case Type.Nothing        => s("Nothing")
      case Type.Func(from, to) => s(from, " => ", to)
      case Type.Rec(fields)    =>
        if (fields.isEmpty) s("{}")
        else s("{ ", r(fields.toList.map { case (k, t) => s(k, ": ", t) }, ","), " }")
    }
  }

  sealed trait Stmt extends Tree
  object Stmt {
    case class Val(name: Name, typ: Type, value: Term) extends Stmt
    case class Import(from: Term, sels: List[Sel]) extends Stmt

    implicit val show: Show[Stmt] = Show {
      case Val(n, t, value)   => s("val ", n, ": ", t, " = ", value)
      case Import(from, sels) => s("import ", from, ".{", r(sels, ", "), "}")
      case t: Term            => s(t)
    }
  }

  sealed trait Term extends Stmt { def tpe: Option[Type] }
  object Term {
    case class Ascribe(value: Term, typ: Type, tpe: Option[Type] = None) extends Term
    case class Func(name: Name, typ: Type, value: Term, tpe: Option[Type] = None) extends Term
    case class Block(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class New(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class Apply(fun: Term, arg: Term, tpe: Option[Type] = None) extends Term
    case class Select(prefix: Term, name: Name, tpe: Option[Type] = None) extends Term
    case class Ident(name: Name, tpe: Option[Type] = None) extends Term
    case class If(cond: Term, thenp: Term, elsep: Term, tpe: Option[Type] = None) extends Term
    case object True extends Term { val tpe = Some(Type.Bool) }
    case object False extends Term { val tpe = Some(Type.Bool) }

    implicit val show: Show[Term] = Show { t =>
      val raw = t match {
        case Ascribe(term, typ, _)     => s(term, ": ", typ)
        case Func(x, t, value, _)      => s("(", x, ": ", t, ") => ", value)
        case Block(Nil, _)             => s("{}")
        case Block(stats, _)           => s("{ ", r(stats.map(i(_)), " "), n("}"))
        case New(Nil, _)               => s("new {}")
        case New(stats, _)             => s("new { ", r(stats.map(i(_))), n("}"))
        case Apply(f, arg, _)          => s(f, "(", arg, ")")
        case Select(pre, name, _)      => s(pre, ".", name)
        case Ident(name, _)            => s(name)
        case If(cond, thenp, elsep, _) => s("if ", cond, " then ", thenp, " else ", elsep)
        case True                      => s("true")
        case False                     => s("false")
      }
      t.tpe.map { tpe => s("<", raw, "> :: ", tpe, "") }.getOrElse(raw)
    }
  }

  sealed trait Sel extends Tree
  object Sel {
    case class Rename(from: Name, to: Name) extends Sel
    case class Exclude(name: Name) extends Sel
    case object Wildcard extends Sel

    implicit val show: Show[Sel] = Show {
      case n: Name         => Tree.show(n)
      case Rename(fr, to)  => s(fr, " => ", to)
      case Exclude(n)      => s(n, " => _")
      case Wildcard        => s("_")
    }
  }

  implicit val show: Show[Tree] = Show {
    case t: Type => s(t)
    case t: Stmt => s(t)
    case t: Name => s(t)
    case t: Sel  => s(t)
  }
}
import Tree._, Stmt._, Term._

object abort { def apply(msg: String): Nothing = throw new Exception(msg) }

object parse extends StandardTokenParsers {

  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>", ".", "=", ",", ";")
  lexical.reserved   ++= List("new", "val", "import", "macro", "_", "Bool", "true", "false", "if", "then", "else")

  def name:   Parser[Name]  = ident                                ^^ { s => Name(s) }
  def id:     Parser[Ident] = name                                 ^^ { n => Ident(n) }
  def bool:   Parser[Term]  = ("true" ^^^ True) | ("false" ^^^ False)
  def block:  Parser[Block] = "{" ~> rep(stmt) <~ "}"              ^^ { stats => Block(stats) }
  def `new`:  Parser[New]   = "new" ~> "{" ~> rep(stmt) <~ "}"     ^^ { stats => New(stats) }
  def func:   Parser[Func]  = ("(" ~> name ~ (":" ~> typ) <~ ")") ~ ("=>" ~> term) ^^ {
                                case x ~ t ~ b => Func(x, t, b)
                              }
  def parens: Parser[Term]  = "(" ~> term <~ ")"
  def `if`:   Parser[Term]  = ("if" ~> term) ~ ("then" ~> term) ~ ("else" ~> term) ^^ {
                                case cond ~ thenp ~ elsep => If(cond, thenp, elsep)
                              }
  def term1:  Parser[Term]  = `if` | bool | id | block | `new` | func | parens
  def term2:  Parser[Term]  = term1 ~ opt("." ~> name)             ^^ { case x ~ y => (x /: y)(Select(_, _)) }
  def term3:  Parser[Term]  = term2 ~ opt("(" ~> term <~ ")")      ^^ { case x ~ y => (x /: y)(Apply(_, _)) }
  def term:   Parser[Term]  = term3 ~ opt(":" ~> typ)              ^^ { case x ~ t => (x /: t)(Ascribe(_, _)) }

  def nameOrWildcard: Parser[Name => Sel] = (name ^^ ((y: Name) => (x: Name) => Sel.Rename(x, y))) |
                                            ("_" ^^^ ((x: Name) => Sel.Exclude(x)))
  def sel: Parser[Sel]  = (name ~ opt("=>" ~> nameOrWildcard)  ^^
                           { case x ~ fopt => fopt.map(f => f(x)).getOrElse(x) }) |
                          ("_" ^^^ Sel.Wildcard)
  def `import`: Parser[Import] = "import" ~> term ~ ("." ~> "{" ~> repsep(sel, ",") <~ "}") ^^ { case from ~ sels => Import(from, sels) }

  def `val`:    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term) ^^ { case x ~ t ~ b => Val(x, t, b) }
  def stmt:     Parser[Stmt]   = `val` | `import` | term

  def tbool: Parser[Type.Bool.type] = "Bool" ^^ { _ => Type.Bool }
  def trec:  Parser[Type.Rec]  = "{" ~> repsep(name ~ (":" ~> typ), ",") <~ "}" ^^ {
    fields => Type.Rec(fields.map { case a ~ b => (a.value, b) }.toMap)
  }
  def typ:   Parser[Type]      = (tbool | trec) ~ rep("=>" ~> trec) ^^ {
    case first ~ rest => rest.foldRight[Type](first)(Type.Func(_, _))
  }

  def program = rep(stmt)

  def as[T](parser: Parser[T])(s: String): ParseResult[T] = phrase(parser)(new lexical.Scanner(new CharSequenceReader(s)))
  def apply(s: String): ParseResult[List[Stmt]] = as(program)(s)
}

object typecheck {
  type Env = Map[String, Type]

  implicit class Subtype(me: Type) {
    def `<:`(other: Type): Boolean = (me, other) match {
      case (a, b) if a == b => true
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case (n, t) =>
          fields2.collectFirst { case (n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
    }
  }

  def intersect[K, V](m1: Map[K, V], m2: Map[K, V])(resolve: (V, V) => V): Map[K, V] =
    m1.toList.collect {
      case (n, tpe) if m2.collectFirst { case (n2, _) if n == n2 => () }.nonEmpty =>
        m2.collectFirst { case (n2, tpe2) => (n, resolve(tpe, tpe2)) }.get
    }.toMap

  def merge[K, V](m1: Map[K, V], m2: Map[K, V])(resolve: (V, V) => V): Map[K, V] = {
    var m = m1
    m2.keys.foreach { k =>
      m = m1 + (k -> m1.get(k).map { v => resolve(v, m2(k)) }.getOrElse(m2(k)))
    }
    m
  }

  def lub(t1: Type, t2: Type): Type = (t1, t2) match {
    case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(intersect(fields1, fields2)(lub))
    case (Type.Bool, Type.Bool)                 => Type.Bool
    case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(glb(s1, t1), lub(s2, t2))
    case _                                      => Type.Rec.empty
  }

  def glb(t1: Type, t2: Type): Type = (t1, t2) match {
    case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(merge(fields1, fields2)(glb))
    case (Type.Bool, Type.Bool)                 => Type.Bool
    case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(lub(s1, t1), glb(s2, t2))
    case _                                      => Type.Nothing
  }

  def imp(from: Term, sels: List[Sel])(implicit env: Env = Map.empty): List[(String, (String, Type))] = {
    val (wildcards, nonwild) = sels.span(_ == Sel.Wildcard)
    println(s"sels: $sels")
    val (exclusions, nonexcluded) = nonwild.span(_.isInstanceOf[Sel.Exclude])
    val members: Map[String, Type] = from.tpe.get match {
      case Type.Rec(members) => members
      case _                 => Map.empty
    }
    def getmember(n: Name): Type = {
      val opt: Option[Type] = members.get(n.value)
      opt.getOrElse { abort(s"can't import $n as it's not defined in $from") }
    }
    wildcards match {
      case Nil =>
        if (exclusions.nonEmpty) abort("can't exclude without a wildcard")
        nonexcluded.map {
          case n: Name              => n.value    -> (n.value -> getmember(n))
          case Sel.Rename(from, to) => from.value -> (to.value -> getmember(from))
          case _                    => abort("unreachable")
        }
      case _ :: Nil =>
        def loop(m: Map[String, (String, Type)], ops: List[Sel]): Map[String, (String, Type)] = ops match {
          case Nil                          => m
          case (n: Name) :: rest            => getmember(n); loop(m, rest)
          case Sel.Rename(from, to) :: rest =>
            val tpe = getmember(from)
            loop(m - from.value + (from.value -> (to.value -> tpe)), rest)
          case Sel.Exclude(n) :: rest       => getmember(n); loop(m - n.value, rest)
          case _                            => abort("unreachable")
        }
        loop(members.map { case (k, v) => k -> (k -> v) }, nonwild).toList
      case _ :: _ :: _  =>
        abort("can't have more than one wildcard")
    }
  }

  def stats(ss: List[Stmt])(implicit env: Env = Map.empty): (Env, List[Stmt]) = ss match {
    case Nil => (Map.empty, Nil)
    case Val(n, tpt, body) :: rest =>
      val tn = Name(n.value)
      val ttpt = typ(tpt)
      val bind= tn.value -> ttpt
      val tbody = term(body)(env + bind)
      val (tenv, trest) = stats(rest)(env + bind)
      (tenv + bind, Val(tn, ttpt, tbody) :: trest)
    case Import(from, sels) :: rest =>
      val tfrom = term(from)
      // TODO: validate selectors
      val binds = imp(tfrom, sels).map { case (_, to) => to }
      val (tenv, trest) = stats(rest)(env ++ binds)
      (tenv, Import(tfrom, sels) :: trest)
    case (t: Term) :: rest =>
      val tt = term(t)
      val (tenv, trest) = stats(rest)
      (tenv, tt :: trest)
  }

  def term(tree: Term)(implicit env: Env = Map.empty): Term = tree match {
    case Ident(n, _) =>
      if (!env.contains(n.value)) abort(s"$n is not in scope")
      else Ident(n, tpe = Some(env(n.value)))

    case Func(x, tpt, body, _) =>
      val tx = Name(x.value)
      val ttpt = typ(tpt)
      val tbody = term(body)(env + (tx.value -> ttpt))
      Func(tx, ttpt, tbody, tpe = Some(Type.Func(ttpt, tbody.tpe.get)))

    case Apply(f, arg, _) =>
      val tf = term(f)
      val targ = term(arg)
      tf.tpe.get match {
        case tpe @ Type.Func(from, to) =>
          if (targ.tpe.get `<:` from)
            Apply(tf, targ, tpe = Some(to))
          else
            abort(s"function expected $from but got ${targ.tpe}")
        case _ =>
          abort(s"one can only apply to function values")
      }

    case Block(blockstats, _) =>
      val (_, tstats) = stats(blockstats)
      Block(tstats, tpe = tstats match {
        case _ :+ (t: Term) => t.tpe
        case _              => Some(Type.Rec.empty)
      })

    case New(newstats, _) =>
      val (tenv, tstats) = stats(newstats)
      New(tstats, tpe = Some(Type.Rec(tenv.toMap)))

    case Select(obj, name: Name, _) =>
      val tobj = term(obj)
      val tsel = tobj.tpe.get match {
        case Type.Rec(fields) =>
          fields.collectFirst { case (n, t) if n == name.value => t }.getOrElse {
            abort(s"object doesn't have a field $name")
          }
        case _ =>
          abort(s"can't select from non-object value")
      }
      Select(tobj, Name(name.value), tpe = Some(tsel))

    case Ascribe(t, tpt, _) =>
      val tt = term(t)
      val ttpt = typ(tpt)
      if (tt.tpe.get `<:` ttpt) Ascribe(tt, ttpt, tpe = Some(ttpt))
      else abort("ascripted value isn't a proper supertype")

    case bool @ (True | False) => bool

    case If(cond, thenp, elsep, _) =>
      val tcond = term(cond)
      if (tcond.tpe.get != Type.Bool) abort(s"if condition must be Bool, not ${tcond.tpe}")
      val tthenp = term(thenp)
      val telsep = term(elsep)
      If(tcond, tthenp, telsep, tpe = Some(lub(tthenp.tpe.get, telsep.tpe.get)))
  }

  def typ(tree: Type)(implicit env: Env = Map.empty): Type = tree match {
    case Type.Bool | Type.Nothing => tree
    case Type.Func(from, to)      => Type.Func(typ(from), typ(to))
    // TODO: validate that there no repetion a-la { val x: {} val x: {} }
    case Type.Rec(fields)         => Type.Rec(fields.map { case (n, t) => (n, typ(t)) })
  }
}

object expand {
  sealed trait Transform { def apply(t: Term): Term }
  case class Expansion(f: Term => Term) extends Transform { def apply(t: Term) = f(t) }
  case class Renaming(to: Name) extends Transform {
    def apply(t: Term) = t match {
      case Ident(_, tpe) => Ident(to, tpe)
      case _             => abort("unreachable")
    }
  }

  type Env = Map[String, Transform]

  var renameId = 0
  def rename(n: Name): Name = {
    renameId += 1
    Name(n.value, lex = n.lex.copy(id = renameId))
  }

  var markId = 0
  def mark(t: Tree): Tree = ???

  def stats(trees: List[Stmt])(implicit env: Env = Map.empty): List[Stmt] = trees match {
    case Nil                       => Nil
    case (t: Term) :: rest       => term(t) :: stats(rest)
    case Val(n, t, b) :: rest    =>
      val x = rename(n)
      val newenv = env + ((n.value, Renaming(x)))
      Val(x, typ(t), term(b)(newenv)) :: stats(rest)(newenv)
    case Import(from, sels) :: rest =>
      val efrom = term(from)
      val renamed = typecheck.imp(efrom, sels).map {
        case (from, (to, _)) =>
          val x = rename(Name(to))
          val transform = to -> Renaming(x)
          (transform, Sel.Rename(Name(from), x))
      }
      val esels = renamed.map { case (_, sel) => sel }
      val envupd = renamed.map { case (transform, _) => transform }
      Import(efrom, esels) :: stats(rest)(env ++ envupd)
  }

  def term(tree: Term)(implicit env: Env = Map.empty): Term = tree match {
    case Apply(fun, arg, tpe)    => Apply(term(fun), term(arg), tpe = tpe.map(typ))
    case Block(stats, tpe)       => Block(this.stats(stats), tpe = tpe.map(typ))
    case Select(qual, name, tpe) => Select(term(qual), Name(name.value), tpe = tpe.map(typ))
    case Ascribe(v, t, tpe)      => Ascribe(term(v), typ(t), tpe = tpe.map(typ))
    case New(stats, tpe)         => New(this.stats(stats), tpe = tpe.map(typ))
    case Func(n, t, b, tpe)      =>
      val x = rename(n)
      Func(x, typ(t), term(b)(env + (n.value -> Renaming(x))), tpe = tpe.map(typ))
    case Ident(n, tpe)           =>
      val pre = Ident(n, tpe.map(typ))
      env.get(n.value).map { f => f(pre) }.getOrElse(abort(s"panic, can't resolve $n"))
    case If(cond, thenp, elsep, tpe) => If(term(cond), term(thenp), term(elsep), tpe = tpe.map(typ))
    case bool @ (True | False)   => bool
  }

  def typ(tree: Type)(implicit env: Env = Map.empty): Type = tree match {
    case Type.Bool | Type.Nothing => tree
    case Type.Func(from, to)      => Type.Func(typ(from), typ(to))
    case Type.Rec(fields)         => Type.Rec(fields.map { case (n, t) => (n, typ(t)) })
  }
}

sealed trait Value { final override def toString = Value.show(this).toString }
object Value {
  case object True extends Value
  case object False extends Value
  case class Func(f: Value => Value) extends Value
  case class Obj(fields: Map[String, Value]) extends Value
  object Obj { val empty = Obj(Map.empty) }

  implicit val show: Show[Value] = Show {
    case Value.Func(f)     => s(f.toString)
    case Value.Obj(fields) => s("{", r(fields.toList.map { case (n, v) => s(n, " = ", v.toString) }, ","), "}")
    case Value.True        => s("true")
    case Value.False       => s("false")
  }
}

object eval {
  type Env = List[Map[Int, Value]]

  var steps = 0
  val limit = 100

  def empty = newstack(Nil)

  def default(t: Type): Value = t match {
    case Type.Func(from, to) => Value.Func(identity)
    case Type.Rec(fields)    => Value.Obj(fields.map { case (n, t) => n -> default(t) }.toMap)
    case Type.Bool           => Value.False
    case Type.Nothing        => abort("unreachable")
  }

  def addb(env: Env, binding: (Name, Value)): Env = {
    val (n, v) = binding
    assert(n.lex.id != 0)
    if(env.contains(n.lex.id)) println(s"!!!!!!! entered $n twice")
    val head :: rest = env
    (head + (n.lex.id -> v)) :: rest
  }

  def addbs(env: Env, bindings: List[(Name, Value)]): Env = {
    var env1 = env
    bindings.foreach { b => env1 = addb(env1, b) }
    env1
  }

  def newstack(env: Env): Env =
    Map.empty[Int, Value] :: env

  def lookup(n: Name)(implicit env: Env): Value =
    env.collectFirst { case m if m.contains(n.lex.id) => m(n.lex.id) }.get

  def stats(stats: List[Stmt])(implicit env: Env = empty): List[(String, Value)] = stats match {
    case Nil => Nil
    case v @ Val(name, tpt, body) :: rest =>
      val ebody = eval(body)(addb(env, name -> default(tpt)))
      (name.value -> ebody) :: eval.stats(rest)(addb(env, name -> ebody))
    case Import(t, sels) :: rest =>
      val __ @ (et: Value.Obj) = eval(t)
      val bindings = sels.map {
        case Sel.Rename(from, to) => to -> et.fields(from.value)
        case _                    => abort("unreachable")
      }
      eval.stats(rest)(addbs(env, bindings))
    case (t: Term) :: rest =>
      ("" -> eval(t)) :: eval.stats(rest)
  }

  def apply(term: Term)(implicit env: Env = empty): Value = {
    steps += 1
    if (steps > limit) abort("step limit reached")
    val res: Value = term match {
      case Apply(fun, value, _) =>
        val efun = eval(fun)
        val evalue = eval(value)
        efun match {
          case Value.Func(f) => f(evalue)
          case _             => abort("unreachable")
        }
      case Block(stats, _) =>
        eval.stats(stats) match {
          case _ :+ (("", value)) => value
          case _                  => Value.Obj.empty
        }
      case Select(qual, name, _) =>
        val equal = eval(qual)
        equal match {
          case obj: Value.Obj => obj.fields(name.value)
          case other          => abort("unreachable")
        }
      case Ascribe(t, _, _) => eval(t)
      case Ident(name, _) => lookup(name)
      case New(stats, _) => Value.Obj(eval.stats(stats).filter { case (k, v) => k.nonEmpty }.toMap)
      case Func(name, tpt, body, _) => Value.Func(v => eval(body)(addb(newstack(env), name -> v)))
      case True => Value.True
      case False => Value.False
      case If(cond, thenp, elsep, _) => if (eval(cond) == Value.True) eval(thenp) else eval(elsep)
    }
    //println(s"eval($term) = $res")
    res
  }
}

object Test extends App {
  val parsed = parse("""
    val xx: { y: Bool } = ((xx: Bool) => new { val y: Bool = xx })(false)
    import xx.{y => x}
    if x then (x: Bool) => x else (x: {}) => x
  """)
  println(parsed)
  val (_, tstats) = typecheck.stats(parsed.get)
  println(s"typechecked: $tstats")
  val estats = expand.stats(tstats)
  println(s"expanded: $estats")
  val values = eval.stats(estats)
  println("evaluation:")
  values.foreach {
    case ("", v) => println(v)
    case (n, v)  => println(s"$n = $v")
  }
}
