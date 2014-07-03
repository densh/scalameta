package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds

object util {
  def abort(msg: String): Nothing = throw new Exception(msg)

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

  private val num2sup: Map[Int, String] = Map(
    0 -> "⁰", 1 -> "¹", 2 -> "²", 3 -> "³", 4 -> "⁴",
    5 -> "⁵", 6 -> "⁶", 7 -> "⁷", 8 -> "⁸", 9 -> "⁹"
  )

  private val num2subs: Map[Int, String] = Map(
    0 -> "₀", 1 -> "₁", 2 -> "₂", 3 -> "₃", 4 -> "₄",
    5 -> "₅", 6 -> "₆", 7 -> "₇", 8 -> "₈", 9 -> "₉"
  )

  def superscripted(i: Int): String =
    if (i < 0) "₋" + superscripted(-i)
    else if (i >= 10) subscripted(i/10) + subscripted(i%10)
    else num2sup(i)

  def subscripted(i: Int): String =
    if (i < 0) "₋" + subscripted(-i)
    else if (i >= 10) subscripted(i/10) + subscripted(i%10)
    else num2subs(i)
}
import util._

final case class Lex(id: Int = 0, marks: Set[Int] = Set.empty)
object Lex {
  val empty = Lex()

  implicit val show: Show[Lex] = Show {
    case Lex(id, marks) =>
      val base = if (id != 0) s(subscripted(id)) else s()
      marks.foldRight(base) { case (m, x) => s(x, superscripted(m)) }
  }
}

sealed trait Tree { override def toString = Tree.show(this).toString }
object Tree {
  case class Name(value: String, lex: Lex = Lex.empty) extends Sel
  object Name { implicit val show: Show[Name] = Show { n => s(n.value, n.lex) } }

  sealed trait Type extends Tree
  object Type {
    sealed abstract class Builtin(val name: String) extends Type
    object Builtin { def unapply(b: Builtin): Some[String] = Some(b.name) }
    case class Func(from: Type, to: Type) extends Type
    case class Rec(fields: Map[String, Type]) extends Type
    object Rec { val empty = Rec(Map.empty) }
    case object Bool extends Builtin("Bool")
    case object Nothing extends Builtin("Nothing")
    case object Tree extends Builtin("Tree")
    case object Int extends Builtin("Int")

    implicit def show[T <: Type]: Show[T] = Show {
      case Type.Builtin(name)  => s(name)
      case Type.Func(from, to) => s(from, " => ", to)
      case Type.Rec(fields)    =>
        if (fields.isEmpty) s("{}")
        else s("{ ", r(fields.toList.map { case (k, t) => s(k, ": ", t) }, ","), " }")
    }

    sealed trait Tag[T] { val tpe: Type }
    object Tag {
      def apply[T](t: Type): Tag[T] = new Tag[T] { val tpe = t }
      implicit val intTag: Tag[Int] = Tag(Type.Int)
      implicit val boolTag: Tag[Boolean] = Tag(Type.Bool)
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
    sealed trait Pretyped extends Term
    case class Ascribe(value: Term, typ: Type, tpe: Option[Type] = None) extends Term
    case class Func(name: Name, typ: Type, value: Term, tpe: Option[Type] = None) extends Term
    case class Block(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class New(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class Apply(fun: Term, arg: Term, tpe: Option[Type] = None) extends Term
    case class Select(prefix: Term, name: Name, tpe: Option[Type] = None) extends Term
    case class Ident(name: Name, tpe: Option[Type] = None) extends Term
    case class If(cond: Term, thenp: Term, elsep: Term, tpe: Option[Type] = None) extends Term
    case class Quasiquote(tree: Term) extends Pretyped { val tpe = Some(Type.Tree) }
    case class Integer(value: Int) extends Pretyped { val tpe = Some(Type.Int) }
    case object True extends Pretyped { val tpe = Some(Type.Bool) }
    case object False extends Pretyped { val tpe = Some(Type.Bool) }

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
        case Quasiquote(t: Term)       => s("`", t, "'")
        case True                      => s("true")
        case False                     => s("false")
        case Integer(v)                => s(v.toString)
      }
      t.tpe.map { tpe => s("(", raw, " :: ", tpe, ")") }.getOrElse(raw)
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


trait Convert[From, To] { def apply(from: From): To }
object Convert {
  def apply[From, To](f: From => To): Convert[From, To] =
    new Convert[From, To] { def apply(from: From): To = f(from) }
}

trait Extract[From, To] { def unapply(from: From): Option[To] }
object Extract {
  def apply[From, To](f: PartialFunction[From, To]): Extract[From, To] =
    new Extract[From, To] { def unapply(from: From): Option[To] = f.lift(from) }
}

object parse extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "{", "}", ":", "=>", ".", "=", ",", ";", "`", "'", "$", "-")
  lexical.reserved   ++= List("new", "val", "import", "macro", "_", "Bool", "Tree", "Int", "Nothing",
                              "true", "false", "if", "then", "else")

  def name:   Parser[Name]  = ident                                ^^ { s => Name(s) }
  def id:     Parser[Ident] = name                                 ^^ { n => Ident(n) }
  def num:    Parser[Term]  = opt("-") ~ numericLit                ^^ { case m ~ s => Integer(s.toInt * m.map(_ => -1).getOrElse(1)) }
  def bool:   Parser[Term]  = ("true" ^^^ True) | ("false" ^^^ False)
  def block:  Parser[Block] = "{" ~> repsep(stmt, ";") <~ "}"      ^^ { stats => Block(stats) }
  def `new`:  Parser[New]   = "new" ~> "{" ~> repsep(stmt, ";") <~ "}"     ^^ { stats => New(stats) }
  def func:   Parser[Func]  = ("(" ~> name ~ (":" ~> typ) <~ ")") ~ ("=>" ~> term) ^^ {
                                case x ~ t ~ b => Func(x, t, b)
                              }
  def parens: Parser[Term]  = "(" ~> term <~ ")"
  def qq:     Parser[Term]  = "`" ~> term <~ "'"                   ^^ { t => Quasiquote(t) }

  def `if`:   Parser[Term]  = ("if" ~> term) ~ ("then" ~> term) ~ ("else" ~> term) ^^ {
                                case cond ~ thenp ~ elsep => If(cond, thenp, elsep)
                              }
  def term1:  Parser[Term]  = `if` | bool | id | block | `new` | func | parens | qq | num
  def term2:  Parser[Term]  = term1 ~ opt("." ~> name)             ^^ { case x ~ y => (x /: y)(Select(_, _)) }
  def term3:  Parser[Term]  = term2 ~ opt(":" ~> typ)              ^^ { case x ~ t => (x /: t)(Ascribe(_, _)) }
  def term:   Parser[Term]  = term3 ~ rep(term3)                   ^^ { case x ~ y => (x /: y)(Apply(_, _)) }

  def nameOrWildcard: Parser[Name => Sel] = (name ^^ ((y: Name) => (x: Name) => Sel.Rename(x, y))) |
                                            ("_" ^^^ ((x: Name) => Sel.Exclude(x)))
  def sel: Parser[Sel]  = (name ~ opt("=>" ~> nameOrWildcard)  ^^
                           { case x ~ fopt => fopt.map(f => f(x)).getOrElse(x) }) |
                          ("_" ^^^ Sel.Wildcard)
  def `import`: Parser[Import] = "import" ~> term ~ ("." ~> "{" ~> repsep(sel, ",") <~ "}") ^^ { case from ~ sels => Import(from, sels) }

  def `val`:    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term) ^^ { case x ~ t ~ b => Val(x, t, b) }
  def stmt:     Parser[Stmt]   = `val` | `import` | term

  def tbuiltin: Parser[Type] = "Bool"    ^^ { _ => Type.Bool    } |
                               "Tree"    ^^ { _ => Type.Tree    } |
                               "Int"     ^^ { _ => Type.Int     } |
                               "Nothing" ^^ { _ => Type.Nothing }
  def trec:     Parser[Type] = "{" ~> repsep(name ~ (":" ~> typ), ",") <~ "}" ^^ {
    fields => Type.Rec(fields.map { case a ~ b => (a.value, b) }.toMap)
  }
  def typ0:     Parser[Type] = tbuiltin | trec
  def typ:      Parser[Type] = typ0 ~ rep("=>" ~> typ0) ^^ {
    case first ~ rest =>
      val init :+ last = first :: rest
      init.foldRight[Type](last)(Type.Func(_, _))
  }

  def program = repsep(stmt, ";")

  def as[T](parser: Parser[T])(s: String): ParseResult[T] = phrase(parser)(new lexical.Scanner(new CharSequenceReader(s)))
  def apply(s: String): ParseResult[List[Stmt]] = as(program)(s)
}

object typecheck {
  type Env = Map[String, Type]
  def empty: Env = predefined.signatures

  implicit class Subtype(me: Type) {
    def `<:`(other: Type): Boolean = (me, other) match {
      case (a, b) if a == b => true
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case (n, t) =>
          fields2.collectFirst { case (n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
      case (_, _) => false
    }
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

  def imp(from: Term, sels: List[Sel])(implicit env: Env = empty): List[(String, (String, Type))] = {
    val (wildcards, nonwild) = sels.span(_ == Sel.Wildcard)
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

  def stats(ss: List[Stmt])(implicit env: Env = empty): (Env, List[Stmt]) = ss match {
    case Nil => (Map.empty, Nil)
    case Val(n, tpt, body) :: rest =>
      val ttpt = typ(tpt)
      val bind = n.value -> ttpt
      val tbody = term(body)(env + bind)
      val (tenv, trest) = stats(rest)(env + bind)
      (tenv + bind, Val(n, ttpt, tbody) :: trest)
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

  def term(tree: Term)(implicit env: Env = empty): Term = tree match {
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
            abort(s"function expected $from but got ${targ.tpe.get}")
        case t =>
          abort(s"one can only apply to function values, not $t")
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

    case If(cond, thenp, elsep, _) =>
      val tcond = term(cond)
      if (tcond.tpe.get != Type.Bool) abort(s"if condition must be Bool, not ${tcond.tpe}")
      val tthenp = term(thenp)
      val telsep = term(elsep)
      If(tcond, tthenp, telsep, tpe = Some(lub(tthenp.tpe.get, telsep.tpe.get)))

    case pretpt: Pretyped =>
      pretpt
  }

  def typ(tree: Type)(implicit env: Env = empty): Type = tree match {
    case builtin: Type.Builtin    => builtin
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
  def empty: Env = predefined.transforms

  var renameId = 0
  def rename(n: Name): Name = {
    renameId += 1
    Name(n.value, lex = n.lex.copy(id = renameId))
  }

  var markId = 0
  def mark(t: Tree): Tree = ???

  def stats(trees: List[Stmt])(implicit env: Env = empty): List[Stmt] = trees match {
    case Nil => Nil
    case (t: Term) :: rest => term(t) :: stats(rest)
    case Val(n, t, b) :: rest =>
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

  def term(tree: Term)(implicit env: Env = empty): Term = tree match {
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
    case q: Quasiquote           => q
    case bool @ (True | False)   => bool
    case num: Integer            => num
  }

  def typ(tree: Type)(implicit env: Env = empty): Type = tree match {
    case builtin: Type.Builtin => builtin
    case Type.Func(from, to)   => Type.Func(typ(from), typ(to))
    case Type.Rec(fields)      => Type.Rec(fields.map { case (n, t) => (n, typ(t)) })
  }
}

sealed trait Value { final override def toString = Value.show(this).toString }
object Value {
  val True = Bool(true)
  val False = Bool(false)
  case class Bool(value: Boolean) extends Value
  case class Func(f: Value => Value) extends Value
  case class Obj(fields: Map[String, Value]) extends Value
  object Obj { val empty = Obj(Map.empty) }
  case class Tree(t: Term) extends Value
  case class Int(value: scala.Int) extends Value

  implicit val show: Show[Value] = Show {
    case Value.Func(f)     => s(f.toString)
    case Value.Obj(fields) => s("{", r(fields.toList.map { case (n, v) => s(n, " = ", v.toString) }, ","), "}")
    case Value.Bool(v)     => if (v) s("true") else s("false")
    case Value.Int(v)      => s(v.toString)
    case Value.Tree(t)     => s("`", t, "'")
  }

  implicit val bool2value: Convert[scala.Boolean, Value] = Convert(Value.Bool.apply)
  implicit val int2value: Convert[scala.Int, Value] = Convert(Value.Int.apply)
  implicit val value2bool: Extract[Value, scala.Boolean] = Extract { case Value.Bool(b) => b }
  implicit val value2int: Extract[Value, scala.Int] = Extract { case Value.Int(v) => v }
}

object predefined {
  def binop[A, B, R](f: (A, B) => R)(implicit A: Type.Tag[A], B: Type.Tag[B], R: Type.Tag[R],
                                              EA: Extract[Value, A], EB: Extract[Value, B], CR: Convert[R, Value]): (Type, Value.Func) =
    Type.Func(A.tpe, Type.Func(B.tpe, R.tpe)) -> Value.Func { case EA(a) => Value.Func { case EB(b) => CR(f(a, b)) } }

  def unop[A, R](f: A => R)(implicit A: Type.Tag[A], R: Type.Tag[R],
                                     EA: Extract[Value, A], CR: Convert[R, Value]): (Type, Value.Func) =
    Type.Func(A.tpe, R.tpe) -> Value.Func { case EA(a) => CR(f(a)) }

  val entries = List(
    "add" -> binop { (a: Int, b: Int) => a + b },
    "sub" -> binop { (a: Int, b: Int) => a - b },
    "mul" -> binop { (a: Int, b: Int) => a * b },
    "div" -> binop { (a: Int, b: Int) => a / b },
    "mod" -> binop { (a: Int, b: Int) => a % b },
    "neg" -> unop  { (a: Int)         => -a    },

    "and" -> binop { (a: Boolean, b: Boolean) => a && b },
    "or"  -> binop { (a: Boolean, b: Boolean) => a || b },
    "not" -> unop  { (a: Boolean)             => !a     },

    "eq"  -> binop { (a: Int, b: Int) => a == b },
    "neq" -> binop { (a: Int, b: Int) => a != b },
    "gt"  -> binop { (a: Int, b: Int) => a >  b },
    "gte" -> binop { (a: Int, b: Int) => a >= b },
    "lt"  -> binop { (a: Int, b: Int) => a <  b },
    "lte" -> binop { (a: Int, b: Int) => a <= b }
  )

  val signatures: typecheck.Env = entries.map { case (n, (t, _)) => n -> t }.toMap
  val transforms: expand.Env    = entries.map { case (n, _) => n -> expand.Renaming(expand.rename(Name(n))) }.toMap
  val values: eval.Env          = List(entries.map { case (n, (_, v)) => transforms(n).asInstanceOf[expand.Renaming].to.lex.id -> v }.toMap)
}

object eval {
  type Env = List[Map[Int, Value]]

  var steps = 0
  val limit = 100

  def empty = newstack(predefined.values)

  def default(t: Type): Value = t match {
    case Type.Func(from, to) => Value.Func(identity)
    case Type.Rec(fields)    => Value.Obj(fields.map { case (n, t) => n -> default(t) }.toMap)
    case Type.Bool           => Value.False
    case Type.Int            => Value.Int(0)
    case Type.Tree           => Value.Tree(Term.Block(Nil))
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
      case Quasiquote(t) => Value.Tree(t)
      case Integer(v) => Value.Int(v)
    }
    //println(s"eval($term) = $res")
    res
  }
}

object Test extends App {
  val parsed = parse("""
    val x: Int = neg -1
  """)
  println(parsed.map { p =>
    val pstats = p.mkString("", "\n", "")
    s"parsed:\n$pstats\n"
  }.getOrElse(parsed.toString))
  val (_, tstats) = typecheck.stats(parsed.get)
  val ststats = tstats.map(_.toString).mkString("", "\n", "")
  println(s"typechecked:\n$ststats\n")
  val estats = expand.stats(tstats)
  val sestats = estats.mkString("", "\n", "")
  println(s"expanded:\n$sestats\n")
  val values = eval.stats(estats)
  println("evaluation:")
  values.foreach {
    case ("", v) => println(v)
    case (n, v)  => println(s"$n = $v")
  }
  println()
}
