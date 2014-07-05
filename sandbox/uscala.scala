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
    case object Any extends Builtin("Any")
    case object Bool extends Builtin("Bool")
    case object Int extends Builtin("Int")
    case object Unit extends Builtin("Unit")
    case object Tree extends Builtin("Tree")
    case object Nothing extends Builtin("Nothing")
    case class Func(from: Type, to: Type) extends Type
    case class Rec(fields: Map[String, Type]) extends Type
    object Rec { val empty = Rec(Map.empty) }

    implicit def show: Show[Type] = Show {
      case Type.Builtin(name)  => s(name)
      case Type.Func(from, to) => s(from, " => ", to)
      case Type.Rec(fields)    =>
        if (fields.isEmpty) s("{}")
        else s("{ ", r(fields.toList.map { case (k, t) => s(k, ": ", t) }, ", "), " }")
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
    case class Func(param: Option[(Name, Type)], value: Term, tpe: Option[Type] = None) extends Term
    case class Block(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class New(self: Option[Name], stats: List[Stmt], tpe: Option[Type.Rec] = None) extends Term
    case class Apply(fun: Term, arg: Term, tpe: Option[Type] = None) extends Term
    case class Select(prefix: Term, name: Name, tpe: Option[Type] = None) extends Term
    case class Ident(name: Name, tpe: Option[Type] = None) extends Term
    case class If(cond: Term, thenp: Term, elsep: Term, tpe: Option[Type] = None) extends Term
    case class Quasiquote(tree: Term) extends Pretyped { val tpe = Some(Type.Tree) }
    case class Integer(value: Int) extends Pretyped { val tpe = Some(Type.Int) }
    case object True extends Pretyped { val tpe = Some(Type.Bool) }
    case object False extends Pretyped { val tpe = Some(Type.Bool) }
    case object Unit extends Pretyped { val tpe = Some(Type.Unit) }

    implicit val show: Show[Term] = Show { t =>
      val raw = t match {
        case Ascribe(term, typ, _)     => s(term, ": ", typ)
        case Func(param, value, _)     => s("(", param.map { case (x, t) => s(x, ": ", t) }.getOrElse(s()), ") => ", value)
        case Block(Nil, _)             => s("{}")
        case Block(stats, _)           => s("{ ", r(stats.map(i(_)), " "), n("}"))
        case New(selfopt, stats, _)    => s("new {",
                                            selfopt.map { self => s(" ", self, " => ") }.getOrElse(s()),
                                            r(stats.map(i(_))),
                                            if (stats.nonEmpty) n("}") else s("}"))
        case Apply(f, arg, _)          => s(f, "(", arg, ")")
        case Select(pre, name, _)      => s(pre, ".", name)
        case Ident(name, _)            => s(name)
        case If(cond, thenp, elsep, _) => s("if ", cond, " then ", thenp, " else ", elsep)
        case Quasiquote(t: Term)       => s("`", t, "'")
        case True                      => s("true")
        case False                     => s("false")
        case Integer(v)                => s(v.toString)
        case Unit                      => s("()")
      }
      //t.tpe.map { tpe => s("(", raw, " :: ", tpe, ")") }.getOrElse(raw)
      raw
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
                              "Unit", "Any", "true", "false", "if", "then", "else")

  def name:   Parser[Name]  = ident                                ^^ { Name(_) }
  def id:     Parser[Ident] = name                                 ^^ { Ident(_) }
  def num:    Parser[Term]  = opt("-") ~ numericLit                ^^ { case m ~ s => Integer(s.toInt * m.map(_ => -1).getOrElse(1)) }
  def bool:   Parser[Term]  = ("true" ^^^ True) | ("false" ^^^ False)
  def block:  Parser[Block] = "{" ~> repsep(stmt, ";") <~ "}"      ^^ { stats => Block(stats) }
  def `new`:  Parser[New]   = "new" ~> "{" ~> opt(name <~ "=>") ~ repsep(stmt, ";") <~ "}" ^^ {
                                case selfopt ~ stats => New(selfopt, stats)
                              }
  def func:   Parser[Func]  = ("(" ~> opt(name ~ (":" ~> typ)) <~ ")") ~ ("=>" ~> term) ^^ {
                                case None ~ b        => Func(None, b)
                                case Some(x ~ t) ~ b => Func(Some((x, t)), b)
                              }
  def parens: Parser[Term]  = "(" ~> opt(term) <~ ")"              ^^ { _.getOrElse(Term.Unit) }
  def qq:     Parser[Term]  = "`" ~> term <~ "'"                   ^^ { Quasiquote(_) }

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

  def tbuiltin: Parser[Type] = ("Bool"    ^^^ Type.Bool    |
                                "Tree"    ^^^ Type.Tree    |
                                "Int"     ^^^ Type.Int     |
                                "Nothing" ^^^ Type.Nothing |
                                "Unit"    ^^^ Type.Unit    |
                                "Any"     ^^^ Type.Any     )
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
      case (_, Type.Any)                          => true
      case (a, b) if a == b                       => true
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case (n, t) =>
          fields2.collectFirst { case (n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
      case (_, _) => false
    }
  }

  def lub(t1: Type, t2: Type): Type = (t1, t2) match {
    case (a, b) if a == b                       => a
    case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(intersect(fields1, fields2)(lub))
    case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(glb(s1, t1), lub(s2, t2))
    case _                                      => Type.Any
  }

  def glb(t1: Type, t2: Type): Type = (t1, t2) match {
    case (a, b) if a == b                       => a
    case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(merge(fields1, fields2)(glb))
    case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(lub(s1, t1), glb(s2, t2))
    case _                                      => Type.Nothing
  }

  // TODO: validate selectors
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

  // TODO: fail on forward references in blocks
  def stats(ss: List[Stmt], self: Option[Option[Name]] = None)(implicit env: Env = empty): (Type.Rec, List[Stmt]) = {
    val scope = ss.collect {
      case Val(n, tpt, _)   => n.value -> tpt
    }.toMap

    val scopethis =
      self.map { selfopt =>
        scope + (selfopt.map(_.value).getOrElse("this") -> Type.Rec(scope))
      }.getOrElse(scope)

    def loop(ss: List[Stmt])(implicit env: Env): List[Stmt] = ss match {
      case Nil => Nil
      case Val(n, tpt, body) :: rest =>
        val ttpt = typ(tpt)
        val tbody = term(body)
        if (tbody.tpe.get `<:` ttpt) Val(n, ttpt, tbody) :: loop(rest)
        else abort(s"body type ${tbody.tpe.get} isn't a subtype of ascribed type $ttpt")
      case Import(from, sels) :: rest =>
        val tfrom = term(from)
        val binds = imp(tfrom, sels).map { case (_, to) => to }
        Import(tfrom, sels) :: loop(rest)(env ++ binds)
      case (t: Term) :: rest =>
        term(t) :: loop(rest)
    }

    (Type.Rec(scope.toMap), loop(ss)(env ++ scopethis))
  }

  def term(tree: Term)(implicit env: Env = empty): Term = tree match {
    case Ident(n, _) =>
      if (!env.contains(n.value)) abort(s"$n is not in scope")
      else Ident(n, tpe = Some(env(n.value)))

    case Func(param, body, _) =>
      val (tparam, ttpt, tbody) = param.map { case (x, tpt) =>
        val tx = Name(x.value)
        val ttpt = typ(tpt)
        val tbody = term(body)(env + (tx.value -> ttpt))
        (Some((tx, ttpt)), ttpt, tbody)
      }.getOrElse {
        val tbody = term(body)
        (None, Type.Unit, tbody)
      }
      Func(tparam, tbody, tpe = Some(Type.Func(ttpt, tbody.tpe.get)))

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
      val (_, tstats) = stats(blockstats, self = None)
      Block(tstats, tpe = tstats match {
        case _ :+ (t: Term) => t.tpe
        case _              => Some(Type.Rec.empty)
      })

    case New(selfopt, newstats, _) =>
      val (trec, tstats) = stats(newstats, self = Some(selfopt))
      New(selfopt, tstats, tpe = Some(trec))

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
      else abort(s"acsribed value of type ${tt.tpe.get} isn't a proper supertype of $ttpt")

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

  def stats(trees: List[Stmt], self: Option[(Option[Name], Type.Rec)] = None)(implicit env: Env = empty): (Option[Name], List[Stmt]) = {
    val (thisrename, nstats, transforms) =
      self.map { case (nameopt, thistpe) =>
        val thisrename = rename(nameopt.getOrElse(Name("this")))
        val thistransform = Renaming(thisrename)
        val firstrun = trees.map {
          case Val(n, t, b) =>
            (Val(n, t, b),
              Some(n.value ->
                Expansion(_ =>
                  Select(Ident(thisrename, tpe = Some(thistpe)), n, tpe = Some(thistpe.fields(n.value))))))
          case other => (other, None)
        }
        val preprocessed = firstrun.map { case (t, _) => t }
        val transforms: List[(String, Transform)] = (firstrun.flatMap { case (_, t) => t }) :+ ("this" -> thistransform)
        (Some(thisrename), preprocessed, transforms)
      }.getOrElse  {
        val firstrun = trees.map {
          case Val(n, t, b) =>
            val x = rename(n)
            (Val(x, t, b), Some(n.value -> Renaming(x)))
          case other => (other, None)
        }
        val preprocessed = firstrun.map { case (t, _) => t }
        val transforms: List[(String, Transform)] = (firstrun.flatMap { case (_, t) => t })
        (None, preprocessed, transforms)
      }

    def loop(trees: List[Stmt])(implicit env: Env): List[Stmt] = trees match {
      case Nil => Nil
      case (t: Term) :: rest =>
        term(t) :: loop(rest)
      case Val(n, t, b) :: rest =>
        Val(n, t, term(b)) :: loop(rest)
      case Import(from, sels) :: rest =>
        val efrom = term(from)
        val envupd = typecheck.imp(efrom, sels).map {
          case (nfrom, (nto, tpe)) => nto -> Expansion(_ => Select(efrom, Name(nfrom), tpe = Some(tpe)))
        }
        loop(rest)(env ++ envupd)
    }
    (thisrename, loop(nstats)(env ++ transforms))
  }

  def term(tree: Term)(implicit env: Env = empty): Term = tree match {
    case Apply(fun, arg, tpe) =>
      Apply(term(fun), term(arg), tpe)
    case Block(stats, tpe) =>
      val (_, nstats) = this.stats(stats, self = None)
      Block(nstats, tpe)
    case Select(qual, name, tpe) =>
      Select(term(qual), Name(name.value), tpe)
    case Ascribe(v, t, tpe) =>
      Ascribe(term(v), t, tpe)
    case New(selfopt, stats, tpe) =>
      val (nself, nstats) = this.stats(stats, self = Some((selfopt, tpe.get)))
      New(nself, nstats, tpe)
    case Func(param, b, tpe) =>
      param.map { case (n, t) =>
        val x = rename(n)
        Func(Some(x, t), term(b)(env + (n.value -> Renaming(x))), tpe)
      }.getOrElse {
        Func(None, term(b), tpe)
      }
    case Ident(n, tpe) =>
      val pre = Ident(n, tpe)
      env.get(n.value).map { f => f(pre) }.getOrElse(abort(s"panic, can't resolve $n"))
    case If(cond, thenp, elsep, tpe) =>
      If(term(cond), term(thenp), term(elsep), tpe)
    case pretpt: Pretyped => pretpt
  }
}

sealed trait Value { final def show(implicit store: eval.Store): String = Value.show(store).apply(this).toString }
object Value {
  sealed trait Stack extends Value
  object Stack {
    implicit def show(implicit store: eval.Store): Show[Value.Stack] = Show {
      case Value.Unit    => s("()")
      case Value.Bool(v) => if (v) s("true") else s("false")
      case Value.Int(v)  => s(v.toString)
      case Value.Ptr(id) => s("#", id.toString, if (id != 0) s(" @ ", store(id)) else s())
    }
  }
  case class Int(value: scala.Int) extends Stack
  case class Ptr(id: scala.Int) extends Stack
  case object Unit extends Stack
  case class Bool(value: Boolean) extends Stack
  val True = Bool(true)
  val False = Bool(false)
  val Null = Ptr(0)

  sealed trait Ref extends Value
  object Ref {
    implicit def show(implicit store: eval.Store): Show[Value.Ref] = Show {
      case Value.Func(_)     => s("ƒ")
      case Value.Tree(t)     => s("`", t, "'")
      case Value.Obj(fields) => s("{", r(fields.toList.map { case (n, v) => s(n, " = ", v) }, ", "), "}")
    }
  }
  case class Func(f: eval.Res => eval.Res) extends Ref
  case class Tree(t: Term) extends Ref
  case class Obj(fields: Map[String, Value.Stack]) extends Ref
  object Obj {
    val empty = Obj(Map.empty)
    implicit val show: Show[Obj] = Show { obj =>
      s("{", r(obj.fields.toList.map { case (n, v) => s(n, " = ", v.toString) }, ","), "}")
    }
  }

  implicit def show(implicit store: eval.Store): Show[Value] = Show {
    case v: Value.Stack => s(v)
    case v: Value.Ref   => s(v)
  }

  implicit val bool2value: Convert[scala.Boolean, Value.Stack] = Convert(Value.Bool.apply)
  implicit val int2value: Convert[scala.Int, Value.Stack] = Convert(Value.Int.apply)
  implicit val value2bool: Extract[Value.Stack, scala.Boolean] = Extract { case Value.Bool(b) => b }
  implicit val value2int: Extract[Value.Stack, scala.Int] = Extract { case Value.Int(v) => v }
}

object predefined {
  import eval.Res

  def binop[A, B, R](f: (A, B) => R)(implicit A: Type.Tag[A], B: Type.Tag[B], R: Type.Tag[R],
                                              EA: Extract[Value.Stack, A], EB: Extract[Value.Stack, B],
                                              CR: Convert[R, Value.Stack]): (Type, Value.Func) =
    Type.Func(A.tpe, Type.Func(B.tpe, R.tpe)) ->
      Value.Func { case Res(EA(a), s1) =>
        s1.alloc(Value.Func { case Res(EB(b), s2) => Res(CR(f(a, b)), s2) })
      }

  def unop[A, R](f: A => R)(implicit A: Type.Tag[A], R: Type.Tag[R],
                                     EA: Extract[Value.Stack, A], CR: Convert[R, Value.Stack]): (Type, Value.Func) =
    Type.Func(A.tpe, R.tpe) -> Value.Func { case Res(EA(a), s) => Res(CR(f(a)), s) }

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

  val signatures = entries.map { case (n, (t, _)) => n -> t }.toMap
  val transforms = entries.map { case (n, _) => n -> expand.Renaming(expand.rename(Name(n))) }.toMap
  val funcvalues = entries.map { case (n, (_, v)) => transforms(n).asInstanceOf[expand.Renaming].to.lex.id -> v }.toMap
}

object eval {
  def abort(msg: String)(implicit env: Env) = uscala.util.abort(s"$msg (${env.store})")

  final case class Store(objs: Map[Int, Value.Ref] = Map.empty, newid: Int = 1) {
    def alloc(v: Value.Ref): Res = {
      Res(Value.Ptr(newid), Store(objs + (newid -> v), newid + 1))
    }
    def apply(id: Int): Value.Ref =  {
      assert(id != 0)
      objs(id)
    }
    def put(id: Int, v: Value.Ref): Store = {
      assert(id != 0)
      assert(objs.contains(id));
      Store(objs + (id -> v), newid)
    }
    def mapOn(id: Int)(f: Value.Ref => Value.Ref): Store = {
      val v = apply(id)
      put(id, f(v))
    }
  }
  final case class Env(stack: List[Map[Int, Value.Stack]], store: Store) {
    require(stack.nonEmpty)

    def bind(name: Name, value: Value.Stack): Env = {
      assert(name.lex.id != 0, s"name id can't be 0 (name = $name)")
      val head :: tail = stack
      Env((head + (name.lex.id -> value)) :: tail, store)
    }
    def bind(bindings: List[(Name, Value.Stack)]): Env = {
      var env = this
      bindings.foreach { case (n, v) => env = env.bind(n, v) }
      env
    }
    def push(): Env =
      Env(Map.empty[Int, Value.Stack] :: stack, store)
    def lookup(n: Name): Value.Stack =
      stack.collectFirst { case m if m.contains(n.lex.id) => m(n.lex.id) }.getOrElse(abort(s"couldn't lookup $n")(this))
  }
  object Env {
    def default = {
      var store = Store()
      var stack = Map.empty[Int, Value.Stack]
      predefined.funcvalues.foreach { case (id, f) =>
        val Res(ref, newstore) = store.alloc(f)
        store = newstore
        stack = stack + (id -> ref)
      }
      Env(stack :: Nil, store)
    }
  }
  final case class Res(value: Value.Stack, store: Store) {
    override def toString = Value.show(store).apply(value).toString
  }

  def default(t: Type): Value.Stack = t match {
    case Type.Rec(_)     |
         Type.Func(_, _) |
         Type.Tree       |
         Type.Any        => Value.Ptr(0)
    case Type.Bool       => Value.False
    case Type.Int        => Value.Int(0)
    case Type.Unit       => Value.Unit
    case Type.Nothing    => abort("unreachable")(null)
  }

  def stats(stats: List[Stmt], self: Option[Name] = None)(implicit env: Env = Env.default): Res = {
    val (nenv, selfrefopt) = self.map { n =>
      val Res(ref: Value.Ptr, s) = env.store.alloc(Value.Obj(stats.collect {
        case Val(n, tpt, _) => n.value -> this.default(tpt)
      }.toMap))
      (env.bind(n, ref).copy(store = s), Some(ref))
    }.getOrElse((env, None))

    def loop(stats: List[Stmt])(implicit env: Env): Res = stats match {
      case Nil =>
        Res(Value.Unit, env.store)
      case v @ Val(name, tpt, body) :: rest =>
        val res = eval(body)
        val store = selfrefopt.map { selfref =>
          res.store.mapOn(selfref.id) { case Value.Obj(fields) =>
            Value.Obj(fields + (name.value -> res.value))
          }
        }.getOrElse(res.store)
        val nenv = selfrefopt.map { _ => env }.getOrElse(env.bind(name, res.value)).copy(store = store)
        loop(rest)(nenv)
      case (t: Term) :: rest =>
        val res = eval(t)
        if (rest.isEmpty) res
        else loop(rest)(env.copy(store = res.store))
      case (_: Import) :: rest =>
        abort("unreachable")
    }

    val res = loop(stats)(nenv)
    selfrefopt.map { selfref =>
      Res(selfref, res.store)
    }.getOrElse(res)
  }

  def apply(term: Term)(implicit env: Env = Env.default): Res = {
    term match {
      case Apply(fun, value, _) =>
        val Res(efun, s1) = eval(fun)
        val Res(evalue, s2) = eval(value)(env.copy(store = s1))
        efun match {
          case Value.Ptr(0) =>
            abort("tried to invoke function that was null pointer")
          case Value.Ptr(id) =>
            val Value.Func(f) = s2(id)
            f(Res(evalue, s2))
          case _             => abort(s"unreachable")
        }
      case Select(qual, name, _) =>
        eval(qual) match {
          case Res(Value.Ptr(0), _ ) =>
            abort("called accessor on null pointer")
          case Res(Value.Ptr(id), s) =>
            val Value.Obj(fields) = s(id)
            Res(fields(name.value), s)
          case other =>
            abort("unreachable")
        }
      case Ident(name, _) =>
        Res(env.lookup(name), env.store)
      case Block(stats, _) =>
        eval.stats(stats)
      case New(nameopt, stats, _) =>
        eval.stats(stats, self = nameopt)
      case Func(param, body, _) =>
        val fvalue =
          param.map { case (name, tpt) =>
            Value.Func(r => eval(body)(env.copy(store = r.store).push().bind(name, r.value)))
          }.getOrElse {
            Value.Func(r => eval(body)(env.copy(store = r.store).push()))
          }
        env.store.alloc(fvalue)
      case If(cond, thenp, elsep, _) =>
        val Res(econd, s) = eval(cond)
        val branch = if (econd == Value.True) thenp else elsep
        eval(branch)(env.copy(store = s))
      case Quasiquote(t)    =>
        val qvalue = Value.Tree(t)
        env.store.alloc(qvalue)
      case Ascribe(t, _, _) => eval(t)
      case True             => Res(Value.True, env.store)
      case False            => Res(Value.False, env.store)
      case Integer(v)       => Res(Value.Int(v), env.store)
      case Unit             => Res(Value.Unit, env.store)
    }
  }
}

object Test extends App {
  val parsed = parse("""
    val testfib: {} = new {
      val fib: Int => Int = (x: Int) =>
        if eq x 0 then 1
        else if eq x 1 then 1
        else mul x (fib (sub x 1));
      val fibeq: Int => Int => Bool = (x: Int) => (exp: Int) => {
        val tmp: Int = fib(x);
        eq tmp exp
      };
      val five: Unit => Int = () => 5;
      val fib5eq120: Bool = fibeq (five ()) 120
    };
    val testany: {} = new {
      val x: Any = if true then 1 else new {}
    }

  """)
  println(parsed.map { p =>
    val pstats = p.mkString("", "\n", "")
    s"parsed:\n$pstats\n"
  }.getOrElse(parsed.toString))

  val root = Some(Name("_root_"))
  val (troot, tstats) = typecheck.stats(parsed.get, self = Some(root))
  println(s"typechecked:\n${tstats.map(_.toString).mkString("", "\n", "")}\n")

  val (rroot, estats) = expand.stats(tstats, self = Some((root, troot)))
  println(s"expanded:\n${estats.mkString("", "\n", "")}\n")

  val res = eval.stats(estats, self = rroot)
  println(s"evaluated: $res")
}
