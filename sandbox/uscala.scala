package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds
import Tree._, Stmt._, Term._
import util._
import semantic._
import Lex.{Mark, Rename}

object util {
  def abort(msg: String): Nothing = throw new Exception(msg)
  def unreachable: Nothing = abort("unreachable")

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

final case class Lex(ops: List[Lex.Op] = Nil) {
  def ::(op: Lex.Op) = Lex(op :: ops)

  def marks: Set[Int] = ops match {
    case Nil                  => Set()
    case Rename(_, _) :: rest => Lex(rest).marks
    case Mark(i) :: rest      =>
      val rmarks = Lex(rest).marks
      if (rmarks.contains(i)) rmarks - i else rmarks + i
  }
}
object Lex {
  sealed trait Op
  final case class Rename(from: Name, to: Name) extends Op { override def toString = s"$from ~> $to" }
  final case class Mark(id: Int) extends Op { override def toString = s"^$id" }

  implicit val show: Show[Lex] = Show { lex =>
    s(lex.marks.map(superscripted).mkString("", "⁺", ""))
  }
}

sealed trait Tree { override def toString = Tree.show(this).toString }
object Tree {
  case class Name(value: String, id: Int = 0, lex: Lex = Lex()) extends Tree {
    def resolve: Name = lex match {
      case Lex(Nil) =>
        this
      case Lex((_: Mark) :: rest) =>
        Name(value, id, Lex(rest)).resolve
      case Lex((r @ Rename(from, to)) :: rest) =>
        val rfrom = from.resolve
        val rrest = Name(value, id, Lex(rest)).resolve
        val c1 = rfrom.value    == rrest.value
        val c2 = rfrom.id       == rrest.id
        val c3 = from.lex.marks == Lex(rest).marks
        if (c1 && c2 && c3) to else rrest
    }
  }
  object Name {
    implicit val show: Show[Name] = Show { n =>
      s(n.value, if (n.id != 0) s(subscripted(n.id)) else s(), n.lex)
    }
  }

  case class Param(name: Name, typ: Type) extends Tree
  object Param { implicit val show: Show[Param] = Show { p => s(p.name, ": ", p.typ) } }

  sealed trait Type extends Tree
  object Type {
    sealed abstract class Builtin(val name: String) extends Type
    object Builtin { def unapply(b: Builtin): Some[String] = Some(b.name) }
    case object Any extends Builtin("Any")
    case object Bool extends Builtin("Bool")
    case object Int extends Builtin("Int")
    case object Unit extends Builtin("Unit")
    case object Term extends Builtin("Term")
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
    case class Macro(name: Name, params: List[Param], res: Type, body: Term) extends Stmt
    case class Import(from: Term) extends Stmt

    implicit val show: Show[Stmt] = Show {
      case Val(n, t, value)       => s("val ", n, ": ", t, " = ", value)
      case Macro(n, params, t, b) => s("macro ", n, "(", r(params, ", "), "): ", t, " = ", b)
      case Import(from)           => s("import ", from, "._")
      case t: Term                => s(t)
    }
  }

  sealed trait Term extends Stmt { def tpe: Option[Type] }
  object Term {
    sealed trait Pretyped extends Term
    case class Ident(name: Name, tpe: Option[Type] = None) extends Term
    case class Ascribe(value: Term, typ: Type, tpe: Option[Type] = None) extends Term
    case class Func(param: Option[Param], value: Term, tpe: Option[Type] = None) extends Term
    case class Block(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class New(self: Option[Name], stats: List[Stmt], tpe: Option[Type.Rec] = None) extends Term
    case class Apply(fun: Term, arg: Term, tpe: Option[Type] = None) extends Term
    case class Select(prefix: Term, name: Name, tpe: Option[Type] = None) extends Term
    case class If(cond: Term, thenp: Term, elsep: Term, tpe: Option[Type] = None) extends Term
    case class Quote(term: Term) extends Pretyped { val tpe = Some(Type.Term) }
    case class Unquote(term: Term) extends Pretyped { val tpe = None }
    case class Integer(value: Int) extends Pretyped { val tpe = Some(Type.Int) }
    case object True extends Pretyped { val tpe = Some(Type.Bool) }
    case object False extends Pretyped { val tpe = Some(Type.Bool) }
    case object Unit extends Pretyped { val tpe = Some(Type.Unit) }

    implicit val show: Show[Term] = Show { t =>
      val raw = t match {
        case Ascribe(term, typ, _)     => s(term, ": ", typ)
        case Func(param, value, _)     => s("(", param.map(s(_)).getOrElse(s()), ") => ", value)
        case Block(Nil, _)             => s("{}")
        case Block(stats, _)           => s("{ ", r(stats.map(i(_)), ";"), n("}"))
        case New(selfopt, stats, _)    => s("new {",
                                            selfopt.map { self => s(" ", self, " => ") }.getOrElse(s()),
                                            r(stats.map(i(_)), ";"),
                                            if (stats.nonEmpty) n("}") else s("}"))
        case Apply(f, arg, _)          => s(f, "(", arg, ")")
        case Select(pre, name, _)      => s(pre, ".", name)
        case Ident(n, _)               => s(n)
        case If(cond, thenp, elsep, _) => s("if ", cond, " then ", thenp, " else ", elsep)
        case Quote(t)                  => s("`", t, "'")
        case Unquote(Ident(n, _))      => s("$", n)
        case Unquote(term)             => s("${", term, "}")
        case True                      => s("true")
        case False                     => s("false")
        case Integer(v)                => s(v.toString)
        case Unit                      => s("()")
      }
      //t.tpe.map { tpe => s("(", raw, " :: ", tpe, ")") }.getOrElse(raw)
      raw
    }
  }

  implicit val show: Show[Tree] = Show {
    case t: Type  => s(t)
    case t: Stmt  => s(t)
    case t: Param => s(t)
    case t: Name  => s(t)
  }
}



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
  lexical.reserved   ++= List("new", "val", "import", "macro", "_", "Bool", "Term", "Int", "Nothing",
                              "Unit", "Any", "true", "false", "if", "then", "else")

  def name:    Parser[Name]    = ident                 ^^ { Name(_) }
  def id:      Parser[Ident]   = name                  ^^ { Ident(_) }
  def num:     Parser[Term]    = opt("-") ~ numericLit ^^ { case m ~ s => Integer(s.toInt * m.map(_ => -1).getOrElse(1)) }
  def bool:    Parser[Term]    = ("true"  ^^^ True |
                                 "false" ^^^ False)

  def param: Parser[Param] = name ~ (":" ~> typ) ^^ { case n ~ t => Param(n, t) }

  def block(d: Int):  Parser[Block] = "{" ~> repsep(stmt(d), ";") <~ "}" ^^ { stats => Block(stats) }
  def `new`(d: Int):  Parser[New]   = "new" ~> "{" ~> opt(name <~ "=>") ~ repsep(stmt(d), ";") <~ "}" ^^ {
    case selfopt ~ stats => New(selfopt, stats)
  }
  def func(d: Int):   Parser[Func]  = ("(" ~> opt(param) <~ ")") ~ ("=>" ~> term(d)) ^^ {
    case popt ~ b => Func(popt, b)
  }
  def parens(d: Int):  Parser[Term]    = "(" ~> opt(term(d)) <~ ")"        ^^ { _.getOrElse(Term.Unit) }
  def quote(d: Int):   Parser[Quote]   = "`" ~> term(d = d + 1) <~ "'"     ^^ { t => Quote(t) }
  def unquote(d: Int): Parser[Unquote] = ("$" ~> id                        ^^ { Unquote(_) } |
                                          "$" ~> "{" ~> term(d - 1) <~ "}" ^^ { Unquote(_) } )


  def `if`(d: Int):   Parser[Term]  = ("if" ~> term(d)) ~ ("then" ~> term(d)) ~ ("else" ~> term(d)) ^^ {
    case cond ~ thenp ~ elsep => If(cond, thenp, elsep)
  }
  def term1(d: Int):  Parser[Term]  = {
    val always = `if`(d) | bool | id | block(d) | `new`(d) | func(d) | parens(d) | quote(d) | num
    if (d > 0) always | unquote(d) else always
  }
  def term2(d: Int):  Parser[Term]  = term1(d) ~ opt("." ~> name) ^^ { case x ~ y => (x /: y)(Select(_, _)) }
  def term3(d: Int):  Parser[Term]  = term2(d) ~ opt(":" ~> typ)  ^^ { case x ~ t => (x /: t)(Ascribe(_, _)) }
  def term(d: Int):   Parser[Term]  = term3(d) ~ rep(term3(d))    ^^ { case x ~ y => (x /: y)(Apply(_, _)) }

  def `import`(d: Int): Parser[Import] = "import" ~> term(d) <~ "." <~ "_"                 ^^ { Import(_) }
  def `val`(d: Int):    Parser[Val]    = ("val" ~> name) ~ (":" ~> typ) ~ ("=" ~> term(d)) ^^ {
    case x ~ t ~ b => Val(x, t, b)
  }
  def `macro`(d: Int):  Parser[Macro]  = ("macro" ~> name) ~ ("(" ~> repsep(param, ",") <~ ")") ~ (":" ~> typ) ~ ("=" ~> term(d)) ^^ {
    case n ~ params ~ t ~ b => Macro(n, params, t, b)
  }
  def stmt(d: Int):     Parser[Stmt]   = `val`(d) | `import`(d) | `macro`(d) | term(d)

  def tbuiltin: Parser[Type] = ("Bool"    ^^^ Type.Bool    |
                                "Term"    ^^^ Type.Term    |
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

  def as[T](parser: Parser[T])(s: String): ParseResult[T] = phrase(parser)(new lexical.Scanner(new CharSequenceReader(s)))
  def apply(s: String): ParseResult[Term] = as(term(0))(s)
}

abstract class Transform {
  def stats(ss: List[Stmt]): List[Stmt] = ss.map(stmt)
  def stmt(s: Stmt): Stmt = s match {
    case (t: Term)                 => term(t)
    case Val(n, t, body)           => Val(name(n), typ(t), term(body))
    case Import(from)              => Import(term(from))
    case Macro(n, params, t, body) => Macro(name(n), params.map(param), typ(t), term(body))
  }
  def term(t: Term): Term = t match {
    case True | False | Unit | (_: Integer) => t
    case q @ Quote(body) =>
      object BodyTransform extends Transform {
        override def term(t: Term): Term = t match {
          case u @ Unquote(t) => Unquote(term(t))
          case _              => super.term(t)
        }
      }
      Quote(BodyTransform.term(body))
    case Unquote(unquoted)           => Unquote(unquoted)
    case Ident(n, tpe)               => Ident(name(n), tpe.map(typ))
    case Apply(f, x, tpe)            => Apply(term(f), term(x), tpe.map(typ))
    case Ascribe(t, tpt, tpe)        => Ascribe(term(t), typ(tpt), tpe.map(typ))
    case Block(xs, tpe)              => Block(stats(xs), tpe.map(typ))
    case New(self, xs, tpe)          => New(self.map(name), stats(xs), tpe.map(typ).map { case t: Type.Rec => t; case _ => unreachable })
    case Func(param, body, tpe)      => Func(param.map(this.param), term(body), tpe.map(typ))
    case If(cond, thenp, elsep, tpe) => If(term(cond), term(thenp), term(elsep), tpe.map(typ))
    case Select(qual, n, tpe)        => Select(term(qual), name(n), tpe.map(typ))
  }
  def typ(t: Type): Type = t match {
    case _: Type.Builtin     => t
    case Type.Rec(fields)    => Type.Rec(fields.map { case (k, t) => (k, typ(t)) })
    case Type.Func(from, to) => Type.Func(typ(from), typ(to))
  }
  def name(n: Name): Name = n
  def param(p: Param): Param = Param(name(p.name), typ(p.typ))
}

object semantic {
  implicit class SemanticType(t1: Type) {
    def `<:`(t2: Type): Boolean = (t1, t2) match {
      case (Type.Any, _)                          => true
      case (a, b) if a == b                       => true
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => t1 `<:` s1 && s2 `<:` t2
      case (Type.Rec(fields1), Type.Rec(fields2)) =>
        fields1.forall { case (n, t) =>
          fields2.collectFirst { case (n2, t2) if n == n2 => t2 }.map(_ `<:` t).getOrElse(false)
        }
      case (_, _) => false
    }
    def lub(t2: Type): Type = (t1, t2) match {
      case (a, b) if a == b                       => a
      case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(intersect(fields1, fields2)(_ lub _))
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(s1 glb t1, s2 lub t2)
      case _                                      => Type.Any
    }

    def glb(t2: Type): Type = (t1, t2) match {
      case (a, b) if a == b                       => a
      case (Type.Rec(fields1), Type.Rec(fields2)) => Type.Rec(merge(fields1, fields2)(_ glb _))
      case (Type.Func(s1, s2), Type.Func(t1, t2)) => Type.Func(s1 lub s2, s2 glb t2)
      case _                                      => Type.Nothing
    }
  }
}

object typecheck {
  // todo: infos: Map[Int, Info]
  case class Env(infos: Map[Name, Info] = predefined.infos) {
    def ++(it: Iterable[(Name, Info)]) = Env(infos ++ it)
    def +(name: Name, info: Info) = Env(infos + (name -> info))
    def lookup(n: Name): Option[Info] = {
      infos.get(Name(n.value, n.id)).map {
        case info @ (_: Info.Of | _: Info.Macro) => require(n.id != 0); info
        case info => info
      }
    }
  }
  sealed trait Info { def tpe: Type }
  object Info {
    case class Of(tpe: Type) extends Info
    case class Macro(arity: Int, tpe: Type, expand: (Env, List[Term]) => Term) extends Info
    case class Prefix(prefix: Term, tpe: Type) extends Info
  }

  class Fresh { private var last: Int = 0; def apply(): Int = { last += 1; last } }
  val freshId = new Fresh
  val freshMark = new Fresh

  def mark(term: Term, markId: Int): Term = {
    val m = Mark(markId)
    object MarkTransform extends Transform {
      override def term(t: Term): Term = t match {
        case Quote(t)   => Quote(this.term(t))
        case Unquote(t) => Unquote(this.term(t))
        case _          => super.term(t)
      }
      override def name(n: Name): Name = n.copy(lex = m :: n.lex)
    }
    MarkTransform.term(term)
  }

  def rename[T <: Stmt](s: T, rn: Rename): T = {
    object RenameTransform extends Transform {
      override def term(t: Term): Term = t match {
        case Quote(t)   => Quote(this.term(t))
        case Unquote(t) => Unquote(this.term(t))
        case _          => super.term(t)
      }
      override def name(n: Name): Name = n.copy(lex = rn :: n.lex)
    }
    val res = RenameTransform.stmt(s).asInstanceOf[T]
    res
  }
  def rename[T <: Stmt](s: T, rns: Iterable[Rename]): T =
    rns.foldRight[Stmt](s)((rn, t) => rename(t, rn)).asInstanceOf[T]

  def imp(from: Term)(implicit env: Env = Env()): Map[String, Type] = from.tpe.get match {
    case Type.Rec(members) => members
    case _                 => Map.empty
  }

  // TODO: fail on forward references in blocks
  def stats(ss: List[Stmt], self: Option[Option[Name]] = None)
           (implicit env: Env = Env()): (Option[Rename], Type.Rec, List[Stmt]) = {
    val vals = ss.collect {
      case Val(n, t, _) =>
        (t, Rename(from = n, to = Name(n.value, id = freshId())))
    }
    val valrenames = vals.map { case (_, rn) => rn }
    val valscope = vals.map { case (t, rn) => rn.to -> Info.Of(t) }

    val macros = ss.collect {
      case Macro(n, params, t, body) =>
        val newn = Name(n.value, id = freshId())
        val renameparams = params.map { case Param(pn, t) =>
          val newpn = Name(pn.value, id = freshId())
          val rn = Rename(from = pn, to = newpn)
          val p = Param(newpn, t)
          (rn, p)
        }
        val tparams = renameparams.map { case (_, p) => p }
        val renames = renameparams.map { case (rn, _) => rn }
        val infos = renameparams.map { case (rn, p) => rn.to -> Info.Of(Type.Term) }
        val tbody = term(rename(body, renames))(env ++ infos)
        val mt = params.map(_.typ).foldRight(t) { Type.Func(_, _) }

        val minfo = Info.Macro(params.length, mt, { (appenv, args) =>
          val m = freshMark()
          val margs = args.map(mark(_, m))
          val pre = tparams.zip(margs).map { case (p, marg) => Val(p.name, Type.Term, Quote(marg)) }
          val ebody = Term.Block(pre :+ tbody)
          //println(s"evaluating macro body $ebody")
          val eval.Res(ptr: Value.Ptr, store) = eval.term(ebody)
          val Value.Tree(exp) = store(ptr.id)
          println(s"original expansion: $exp")
          val uexp = mark(exp, m)
          println(s"remarked expansion: $uexp")
          val texp = typecheck.term(uexp)(Env(appenv.infos ++ env.infos))
          println(s"typechecked expansion: $texp")
          if (!(texp.tpe.get `<:` t)) abort(s"macro expansion type ${texp.tpe.get} doesn't conform to $t")
          texp
        })

        (minfo, Rename(from = n, to = newn))
    }
    val macrorenames = macros.map { case (_, rn) => rn }
    val macroscope = macros.map { case (info, rn) => rn.to -> info }

    val thisv  = self.map { _.map(_.value).getOrElse("this") }
    val thisid = freshId()
    val thisrn = thisv.map { v => Rename(from = Name(v), to = Name(v, id = thisid)) }
    val thistpe = Type.Rec(valscope.map { case (n, t) => n.value -> t.tpe }.toMap)
    val thisscope = thisrn.map { rn => rn.to -> Info.Of(thistpe) }

    val renames = valrenames ++ macrorenames ++ thisrn
    val scope = valscope ++ macroscope ++ thisscope

    def loop(ss: List[Stmt])(implicit env: Env): List[Stmt] = ss match {
      case Nil => Nil
      case Val(n, tpt, body) :: rest =>
        val ttpt = typ(tpt)
        val tbody = term(body)
        val tn = n.resolve
        if (tbody.tpe.get `<:` ttpt) Val(tn, ttpt, tbody) :: loop(rest)
        else abort(s"body type ${tbody.tpe.get} isn't a subtype of ascribed type $ttpt")
      case Macro(n, params, t, b) :: rest =>
        loop(rest)
      case Import(from) :: rest =>
        val tfrom = term(from)
        // TODO: rename imported names
        val selected = imp(tfrom).toList
        val infos = selected.map { case (s, t) => Name(s) -> Info.Prefix(tfrom, t) }
        Import(tfrom) :: loop(rest)(env ++ infos)
      case (t: Term) :: rest =>
        term(t) :: loop(rest)
    }

    (thisrn, thistpe, loop(ss.map(rename(_, renames)))(env ++ scope))
  }

  object Applied {
    def unapply(x: Term): Some[(Term, List[Term])] = x match {
      case Apply(Applied(f, args), arg, _) => Some((f, args :+ arg))
      case other                           => Some((other, Nil))
    }
  }

  def term(tree: Term)(implicit env: Env = Env()): Term = {
    val res = tree match {
      case Applied(Ident(n, _), args) if env.lookup(n.resolve).exists(_.isInstanceOf[Info.Macro]) =>
        val r = n.resolve
        val __ @ (info: Info.Macro) = env.lookup(r).get
        // TODO: check that argument types are correct
        if (args.length != info.arity)
          abort(s"macro $r expected ${info.arity} arguments, got ${args.length}")
        val targs = args.map(term(_))
        info.expand(env, args)

      case Ident(Name("scope", _, _), _) =>
        println(s"scope: $env")
        tree

      case Ident(n: Name, _) =>
        val r = n.resolve
        env.lookup(r).getOrElse(abort(s"$n is not in scope")) match {
          case Info.Of(t) =>
            Ident(r, tpe = Some(t))
          case Info.Prefix(pre, t) =>
            Select(pre, r, tpe = Some(t))
          case _: Info.Macro =>
            unreachable
        }

      case Func(param, body, _) =>
        val (tparam, ttpt, tbody) = param.map { case Param(x, tpt) =>
          val ttpt = typ(tpt)
          val pid = freshId()
          val tx = Name(x.value, id = pid)
          val rn = Rename(from = x, to = tx)
          val tbody = term(rename(body, rn))(env + (rn.to, Info.Of(tpt)))
          (Some(Param(tx, ttpt)), ttpt, tbody)
        }.getOrElse {
          val tbody = term(body)
          (None, Type.Unit, tbody)
        }
        Func(tparam, tbody, tpe = Some(Type.Func(ttpt, tbody.tpe.get)))

      case Apply(f, arg, _) =>
        val tf = term(f)
        val targ = term(arg)
        tf.tpe match {
          case Some(tpe @ Type.Func(from, to)) =>
            if (targ.tpe.get `<:` from)
              Apply(tf, targ, tpe = Some(to))
            else
              abort(s"function expected $from but got ${targ.tpe.get} ($tf $targ)")
          case Some(t) =>
            abort(s"one can only apply to function values, not $t")
          case None =>
            abort(s"OOPSIE, $tf")
        }

      case Block(blockstats, _) =>
        val (_, _, tstats) = stats(blockstats, self = None)
        Block(tstats, tpe = tstats match {
          case _ :+ (t: Term) => t.tpe
          case _              => Some(Type.Rec.empty)
        })

      case New(selfopt, newstats, _) =>
        val (thisrn, trec, tstats) = stats(newstats, self = Some(selfopt))
        val Some(Rename(_, to)) = thisrn
        New(Some(to), tstats, Some(trec))

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
        If(tcond, tthenp, telsep, tpe = Some(tthenp.tpe.get lub telsep.tpe.get))

      case q @ Quote(t) =>
        Quote(quoteBody(t))

      case u: Unquote =>
        println(s"encountered unexpected unquote $u")
        unreachable

      case pretpt: Pretyped =>
        pretpt
    }
    res
  }

  def quoteBody(term: Term)(implicit env: Env = Env()): Term = {
    object UnquoteTypecheck extends Transform {
      override def term(t: Term): Term = t match {
        case Unquote(inner) =>
          val tinner = typecheck.term(inner)
          if (tinner.tpe.get `<:` Type.Term) Unquote(tinner)
          else abort(s"unquoted values must be terms, not ${tinner.tpe.get}")
        case _ =>
          super.term(t)
      }
    }
    UnquoteTypecheck.term(term)
  }

  // TODO: validate that there no repetion a-la { val x: {} val x: {} }
  def typ(tree: Type)(implicit env: Env = Env()): Type = tree
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
  implicit val int2value:  Convert[scala.Int, Value.Stack]     = Convert(Value.Int.apply)
  implicit val value2bool: Extract[Value.Stack, scala.Boolean] = Extract { case Value.Bool(b) => b }
  implicit val value2int:  Extract[Value.Stack, scala.Int]     = Extract { case Value.Int(v) => v }
}

object predefined {
  import eval.Res
  import typecheck.Info

  def binop[A, B, R](f: (A, B) => R)(implicit A: Type.Tag[A], B: Type.Tag[B], R: Type.Tag[R],
                                              ToA: Extract[Value.Stack, A], ToB: Extract[Value.Stack, B],
                                              fromR: Convert[R, Value.Stack]): (Type, Value.Func) =
    Type.Func(A.tpe, Type.Func(B.tpe, R.tpe)) ->
      Value.Func { case Res(ToA(a), s1) =>
        s1.alloc(Value.Func { case Res(ToB(b), s2) => Res(fromR(f(a, b)), s2) })
      }

  def unop[A, R](f: A => R)(implicit A: Type.Tag[A], R: Type.Tag[R],
                                     ToA: Extract[Value.Stack, A], fromR: Convert[R, Value.Stack]): (Type, Value.Func) =
    Type.Func(A.tpe, R.tpe) -> Value.Func { case Res(ToA(a), s) => Res(fromR(f(a)), s) }

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

  val predefId = typecheck.freshId()
  val predefName = Name("predef", id = predefId)
  val predefType = Type.Rec(entries.map { case (n, (t, _)) => n -> t }.toMap)
  val predefTerm = Ident(predefName, tpe = Some(predefType))
  val infos = entries.map { case (n, (t, _)) => Name(n) -> Info.Prefix(predefTerm, t) }.toMap + (predefName -> Info.Of(predefType))
  val renames = Rename(Name("predef"), predefTerm.name) :: Nil
  def value(store: eval.Store): Res = {
    var nstore = store
    val funcs = entries.map { case (n, (_, f)) =>
      val Res(ref, newstore) = nstore.alloc(f)
      nstore = newstore
      n -> ref
    }.toMap
    nstore.alloc(Value.Obj(funcs))
  }
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
      assert(name.id != 0, s"name id can't be 0 (name = $name)")
      val head :: tail = stack
      Env((head + (name.id -> value)) :: tail, store)
    }
    def bind(bindings: List[(Name, Value.Stack)]): Env = {
      var env = this
      bindings.foreach { case (n, v) => env = env.bind(n, v) }
      env
    }
    def push(): Env =
      Env(Map.empty[Int, Value.Stack] :: stack, store)
    def lookup(n: Name): Value.Stack =
      stack.collectFirst { case m if m.contains(n.id) => m(n.id) }.getOrElse(abort(s"couldn't lookup $n")(this))
  }
  object Env {
    def default = {
      val Res(predefRef, store) = predefined.value(Store())
      var stack = Map(predefined.predefId -> predefRef)
      Env(stack :: Nil, store)
    }
  }
  final case class Res(value: Value.Stack, store: Store) {
    override def toString = Value.show(store).apply(value).toString
  }

  def default(t: Type): Value.Stack = t match {
    case Type.Rec(_)     |
         Type.Func(_, _) |
         Type.Term       |
         Type.Any        => Value.Ptr(0)
    case Type.Bool       => Value.False
    case Type.Int        => Value.Int(0)
    case Type.Unit       => Value.Unit
    case Type.Nothing    => unreachable
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
        val res = eval.term(body)
        val store = selfrefopt.map { selfref =>
          res.store.mapOn(selfref.id) {
            case Value.Obj(fields) =>
              Value.Obj(fields + (name.value -> res.value))
            case _ =>
              unreachable
          }
        }.getOrElse(res.store)
        val nenv = selfrefopt.map { _ => env }.getOrElse(env.bind(name, res.value)).copy(store = store)
        loop(rest)(nenv)
      case (t: Term) :: rest =>
        val res = eval.term(t)
        if (rest.isEmpty) res
        else loop(rest)(env.copy(store = res.store))
      case (_: Import | _: Macro) :: rest =>
        unreachable
    }

    val res = loop(stats)(nenv)
    selfrefopt.map { selfref =>
      Res(selfref, res.store)
    }.getOrElse(res)
  }

  def term(t: Term)(implicit env: Env = Env.default): Res = t match {
    case Apply(fun, value, _) =>
      val Res(efun, s1) = eval.term(fun)
      val Res(evalue, s2) = eval.term(value)(env.copy(store = s1))
      efun match {
        case Value.Ptr(0) =>
          abort("tried to invoke function that was null pointer")
        case Value.Ptr(id) =>
          val Value.Func(f) = s2(id)
          f(Res(evalue, s2))
        case _             => abort(s"unreachable")
      }
    case Select(qual, name, _) =>
      eval.term(qual) match {
        case Res(Value.Ptr(0), _ ) =>
          abort("called accessor on null pointer")
        case Res(Value.Ptr(id), s) =>
          val Value.Obj(fields) = s(id)
          Res(fields(name.value), s)
        case other =>
          unreachable
      }
    case Ident(name: Name, _) =>
      Res(env.lookup(name), env.store)
    case Block(stats, _) =>
      eval.stats(stats)
    case New(nameopt, stats, _) =>
      eval.stats(stats, self = nameopt)
    case Func(param, body, _) =>
      val fvalue =
        param.map { case Param(name, tpt) =>
          Value.Func(r => eval.term(body)(env.copy(store = r.store).push().bind(name, r.value)))
        }.getOrElse {
          Value.Func(r => eval.term(body)(env.copy(store = r.store).push()))
        }
      env.store.alloc(fvalue)
    case If(cond, thenp, elsep, _) =>
      val Res(econd, s) = eval.term(cond)
      val branch = if (econd == Value.True) thenp else elsep
      eval.term(branch)(env.copy(store = s))
    case q: Quote         => eval.quote(q)
    case _: Unquote       => unreachable
    case Ascribe(t, _, _) => eval.term(t)
    case True             => Res(Value.True, env.store)
    case False            => Res(Value.False, env.store)
    case Integer(v)       => Res(Value.Int(v), env.store)
    case Unit             => Res(Value.Unit, env.store)
  }

  def quote(q: Quote)(implicit env: Env = Env.default): Res = {
    object UnquoteSubs extends Transform {
      var store = env.store
      override def term(t: Term): Term = t match {
        case Unquote(term) =>
          val Res(Value.Ptr(id), nstore) = eval.term(term)(env.copy(store = store))
          store = nstore
          val Value.Tree(t) = store(id)
          t
        case _ =>
          super.term(t)
      }
    }
    val treevalue = Value.Tree(UnquoteSubs.term(q.term))
    UnquoteSubs.store.alloc(treevalue)
  }
}

object Test extends App {
  val parsed = parse("""
    (add: Int => Int => Int) =>
    (x: Int) => {
      macro m(e: Int): Int => Int = `(x: Int) => add $e x';
      m x
    }
  """)
  println(parsed.map { t => s"parsed:\n$t\n" }.getOrElse(parsed.toString))

  val typechecked = typecheck.term(parsed.get)
  println(s"typechecked:\n$typechecked\n")

  val value = eval.term(typechecked)
  println(s"evaluated:\n$value")
}
