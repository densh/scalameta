package uscala

import org.scalameta.show.Show, Show.{ sequence => s, repeat => r, indent => i, newline => n }
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input.CharSequenceReader
import scala.language.higherKinds

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
import util._

sealed trait Tree { override def toString = Tree.show(this).toString }
object Tree {
  case class Name(value: String, lex: Lex = Lex.empty) extends Tree
  object Name { implicit val show: Show[Name] = Show { n => s(n.value, n.lex) } }

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
    case class Ascribe(value: Term, typ: Type, tpe: Option[Type] = None) extends Term
    case class Func(param: Option[Param], value: Term, tpe: Option[Type] = None) extends Term
    case class Block(stats: List[Stmt], tpe: Option[Type] = None) extends Term
    case class New(self: Option[Name], stats: List[Stmt], tpe: Option[Type.Rec] = None) extends Term
    case class Apply(fun: Term, arg: Term, tpe: Option[Type] = None) extends Term
    case class Select(prefix: Term, name: Name, tpe: Option[Type] = None) extends Term
    case class Ident(name: Name, tpe: Option[Type] = None) extends Term
    case class If(cond: Term, thenp: Term, elsep: Term, tpe: Option[Type] = None) extends Term
    case class Quote(term: Term) extends Pretyped { val tpe = Some(Type.Term) }
    case class Unquote(term: Term) extends Pretyped { val tpe = None }
    case class Integer(value: Int) extends Pretyped { val tpe = Some(Type.Int) }
    case object True extends Pretyped { val tpe = Some(Type.Bool) }
    case object False extends Pretyped { val tpe = Some(Type.Bool) }
    case object Unit extends Pretyped { val tpe = Some(Type.Unit) }
    case class Captured(term: Term, env: attribute.Env) extends Term { def tpe = term.tpe }

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
        case Ident(name, _)            => s(name)
        case If(cond, thenp, elsep, _) => s("if ", cond, " then ", thenp, " else ", elsep)
        case Quote(t)                  => s("`", (t: Term), "'")
        case Unquote(id: Ident)        => s("$", (id: Term))
        case Unquote(term)             => s("${", term, "}")
        case True                      => s("true")
        case False                     => s("false")
        case Integer(v)                => s(v.toString)
        case Unit                      => s("()")
        case Captured(t, _)            => s(t)
      }
      //t.tpe.map { tpe => s("(", raw, " :: ", tpe, ")") }.getOrElse(raw)
      raw
    }
  }

  implicit val show: Show[Tree] = Show {
    case t: Type  => s(t)
    case t: Stmt  => s(t)
    case t: Name  => s(t)
    case t: Param => s(t)
  }
}
import Tree._, Stmt._, Term._

final case class Attr(id: Int, tpe: Type, prefix: Option[Term])
final case class Lex(env: Map[String, Attr] = Map.empty, id: Int = 0)
object Lex {
  val empty = Lex()
  implicit val show: Show[Lex] = Show { lex => if (lex.id != 0) s(subscripted(lex.id)) else s() }
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
  def stats(s: List[Stmt]): List[Stmt] = s match {
    case Nil                               => Nil
    case (t: Term) :: rest                 => term(t) :: stats(rest)
    case Val(n, t, body) :: rest           => Val(name(n), typ(t), term(body)) :: stats(rest)
    case Import(from) :: rest              => Import(term(from)) :: stats(rest)
    case Macro(n, params, t, body) :: rest => Macro(name(n), params.map(param), typ(t), term(body)) :: stats(rest)
  }
  def term(t: Term): Term = t match {
    case True | False | Unit         |
         (_: Ident)   | (_: Quote)   |
         (_: Unquote) | (_: Integer) => t
    case Apply(f, x, tpe)            => Apply(term(f), term(x), tpe.map(typ))
    case Ascribe(t, tpt, tpe)        => Ascribe(term(t), typ(tpt), tpe.map(typ))
    case Block(xs, tpe)              => Block(stats(xs), tpe.map(typ))
    case New(self, xs, tpe)          => New(self.map(name), stats(xs), tpe.map(typ).map { case t: Type.Rec => t; case _ => unreachable })
    case Func(param, body, tpe)      => Func(param.map { case Param(n, t) => Param(name(n), typ(t)) }, term(body), tpe.map(typ))
    case If(cond, thenp, elsep, tpe) => If(term(cond), term(thenp), term(elsep), tpe.map(typ))
    case Select(qual, n, tpe)        => Select(term(qual), name(n), tpe.map(typ))
    case Captured(t, env)            => Captured(term(t), env)
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
import semantic._

object attribute {
  type Env = Map[String, Attr]
  def Env(): Env = predefined.attrs

  def imp(from: Term)(implicit env: Env = Env()): Map[String, Type] = from.tpe.get match {
    case Type.Rec(members) => members
    case _                 => Map.empty
  }

  var lastId = 0
  def freshId: Int = {
    lastId += 1
    lastId
  }

  // TODO: fail on forward references in blocks
  def stats(ss: List[Stmt], self: Option[Option[Name]] = None)(implicit env: Env = Env()): (Option[(String, Attr)], Type.Rec, List[Stmt]) = {
    val thisv: Option[String] = self.map { _.map(_.value).getOrElse("this") }
    val thisid   = freshId

    val valscope: Env = ss.collect {
      case Val(n, t, _) =>
        n.value -> Attr(id = freshId, tpe = t,
                        prefix = thisv.map(v => Ident(Name(v, Lex(id = thisid)))))
    }.toMap
    val macroscope: Env = ss.collect {
      case Macro(n, params, t, _) =>
        val mt = params.map(_.typ).foldRight(t) { Type.Func(_, _) }
        n.value -> Attr(id = freshId, tpe = mt, prefix = None)
    }.toMap

    val thistype = Type.Rec(valscope.map { case (n, attr) => n -> attr.tpe })
    val thisbind =
      thisv.map { v =>
        v -> Attr(id = thisid, tpe = thistype, prefix = None)
      }

    val scope: Env = valscope ++ macroscope ++ thisbind

    def loop(ss: List[Stmt])(implicit env: Env): List[Stmt] = ss match {
      case Nil => Nil
      case Val(Name(n, _), tpt, body) :: rest =>
        val ttpt = typ(tpt)
        val tbody = term(body)
        if (tbody.tpe.get `<:` ttpt) Val(Name(n, Lex(id = env(n).id)), ttpt, tbody) :: loop(rest)
        else abort(s"body type ${tbody.tpe.get} isn't a subtype of ascribed type $ttpt")
      case Macro(Name(n, _), params, t, b) :: rest =>
        val attrparams = params.map { case Param(Name(pn, _), t) =>
          val pid = freshId
          val p = Param(Name(pn, Lex(id = pid)), t)
          val attr = Attr(id = pid, tpe = Type.Term, prefix = None)
          (attr, p)
        }
        val tparams = attrparams.map { case (_, p) => p }
        val envupd = attrparams.map { case (attr, p) => p.name.value -> attr }
        Macro(Name(n, Lex(id = env(n).id)), tparams, t, term(b)(env ++ envupd)) :: loop(rest)
      case Import(from) :: rest =>
        val tfrom = term(from)
        val binds = imp(tfrom).toList.map { case (s, t) => s -> Attr(id = freshId, tpe = t, prefix = Some(tfrom)) }
        Import(tfrom) :: loop(rest)(env ++ binds)
      case (t: Term) :: rest =>
        term(t) :: loop(rest)
    }

    (thisbind, thistype, loop(ss)(env ++ scope))
  }

  def term(tree: Term)(implicit env: Env = Env()): Term = tree match {
    case Ident(Name(n, _), _) =>
      if (!env.contains(n)) abort(s"$n is not in scope")
      else Ident(Name(n, lex = Lex(env = env)), tpe = Some(env(n).tpe))

    case Func(param, body, _) =>
      val (tparam, ttpt, tbody) = param.map { case Param(Name(x, _), tpt) =>
        val ttpt = typ(tpt)
        val pid = freshId
        val pattr = Attr(id = pid, tpe = ttpt, prefix = None)
        val tbody = term(body)(env + (x -> pattr))
        (Some(Param(Name(x, Lex(id = pid)), ttpt)), ttpt, tbody)
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
            abort(s"function expected $from but got ${targ.tpe.get} ($tf $targ)")
        case t =>
          abort(s"one can only apply to function values, not $t")
      }

    case Block(blockstats, _) =>
      val (_, _, tstats) = stats(blockstats, self = None)
      Block(tstats, tpe = tstats match {
        case _ :+ (t: Term) => t.tpe
        case _              => Some(Type.Rec.empty)
      })

    case New(selfopt, newstats, _) =>
      val (thisbind, trec, tstats) = stats(newstats, self = Some(selfopt))
      val (n, Attr(id, _, _)) = thisbind.get
      New(Some(Name(n, lex = Lex(id = id))), tstats, tpe = Some(trec))

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

    case Quote(Captured(t, cenv)) =>
      Quote(Captured(quoteBody(t), cenv))

    case Quote(t) =>
      Quote(Captured(quoteBody(t), env))

    case Captured(t, cenv) =>
      Captured(term(t)(env ++ cenv), cenv)

    case _: Unquote =>
      unreachable

    case pretpt: Pretyped =>
      pretpt
  }

  def quoteBody(term: Term)(implicit env: Env = Env()): Term = {
    object UnquoteTypecheck extends Transform {
      override def term(t: Term): Term = t match {
        case Unquote(inner) =>
          val tinner = attribute.term(inner)
          if (tinner.tpe.get `<:` Type.Term) Unquote(tinner)
          else abort(s"unquoted values must be terms, not ${tinner.tpe.get}")
        case _ =>
          super.term(t)
      }
    }
    UnquoteTypecheck.term(term)
  }

  def typ(tree: Type)(implicit env: Env = Env()): Type = tree match {
    case builtin: Type.Builtin    => builtin
    case Type.Func(from, to)      => Type.Func(typ(from), typ(to))
    // TODO: validate that there no repetion a-la { val x: {} val x: {} }
    case Type.Rec(fields)         => Type.Rec(fields.map { case (n, t) => (n, typ(t)) })
  }
}

object expand {
  final case class Tx(arity: Int, f: (attribute.Env, List[Term]) => Term)
  type Env = Map[String, Tx]
  def Env(): Env = Map.empty

  def stats(trees: List[Stmt], self: Option[(Option[Name], Type.Rec)] = None)(implicit env: Env = Env()): List[Stmt] = trees match {
    case Nil => Nil
    case (t: Term) :: rest =>
      term(t) :: this.stats(rest)
    case Val(n, t, b) :: rest =>
      Val(n, t, term(b)) :: this.stats(rest)
    case Import(_) :: rest =>
      this.stats(rest)
    case Macro(n, params, t, body) :: rest =>
      val rbody = term(body)
      val tx = Tx(params.length, { (appenv, args) =>
        val pre = params.zip(args).map { case (p, arg) => Val(p.name, Type.Term, Quote(arg)) }
        val eval.Res(ptr: Value.Ptr, store) = eval.term(Term.Block(pre :+ rbody))
        val Value.Tree(exp) = store(ptr.id)
        val texp = attribute.term(exp)(appenv)
        if (!(texp.tpe.get `<:` t)) abort(s"macro expansion type ${texp.tpe.get} doesn't conform to $t")
        val rexp = expand.term(texp)
        rexp
      })
      this.stats(rest)(env + (n.value -> tx))
  }

  object Applied {
    def unapply(x: Term): Some[(Term, List[Term])] = x match {
      case Apply(Applied(f, args), arg, _) => Some((f, args :+ arg))
      case other                           => Some((other, Nil))
    }
  }

  def term(tree: Term)(implicit env: Env = Env()): Term = tree match {
    case Applied(Ident(Name(n, Lex(lenv, _)), _), args) if env.contains(n) =>
      val Tx(arity, f) = env.get(n).get
      if (args.length != arity)
        abort(s"macro $n expected $arity arguments, got ${args.length}")
      f(lenv, args.map(arg => term(arg)))
    case Ident(Name(_, Lex(_, id)), _) if id != 0 =>
      tree
    case Ident(Name(n, Lex(lenv, id)), tpe) =>
      lenv.get(n).map {
        case Attr(it, _, None) =>
          Ident(Name(n, Lex(id = lenv(n).id)), tpe)
        case Attr(it, _, Some(prefix)) =>
          val tprefix =
            if (prefix.tpe.nonEmpty) prefix
            else attribute.term(prefix)(lenv)
          Select(prefix, Name(n))
      }.getOrElse {
        abort(s"panic, can't resolve $n (${env})")
      }
    case Apply(fun, arg, tpe) =>
      Apply(term(fun), term(arg), tpe)
    case Block(stats, tpe) =>
      val nstats = this.stats(stats, self = None)
      Block(nstats, tpe)
    case Select(qual, name, tpe) =>
      Select(term(qual), Name(name.value), tpe)
    case Ascribe(v, t, tpe) =>
      Ascribe(term(v), t, tpe)
    case New(selfopt, stats, tpe) =>
      val nstats = this.stats(stats, self = Some((selfopt, tpe.get)))
      New(selfopt, nstats, tpe)
    case Func(param, b, tpe) =>
      Func(param, term(b), tpe)
    case If(cond, thenp, elsep, tpe) =>
      If(term(cond), term(thenp), term(elsep), tpe)
    case Captured(t, env) =>
      term(t)
    case q: Quote =>
      quote(q)
    case _: Pretyped => tree
  }

  def quote(q: Quote)(implicit env: Env = Env()): Quote = {
    object ExpandUnquote extends Transform {
      override def term(t: Term): Term = t match {
        case Unquote(term) => Unquote(expand.term(term))
        case _             => super.term(t)
      }
    }
    val Quote(Captured(term, env)) = q
    Quote(Captured(ExpandUnquote.term(term), env))
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

  val attrs = entries.map { case (n, (t, _)) => n -> Attr(id = attribute.freshId, tpe = t, prefix = None) }.toMap
  //val renames    = entries.map { case (n, _) => n -> expand.rename(Name(n)) }.toMap
  //val transforms = renames.map { case (n, (_, tx)) => n -> tx }
  val funcvalues = entries.zip(attrs).map { case ((n, (_, v)), (_, attr)) => attr.id -> v }.toMap
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
    case Ident(name, _) =>
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
    case q: Quote                   => eval.quote(q)
    case (_: Unquote | _: Captured) => unreachable
    case Ascribe(t, _, _)           => eval.term(t)
    case True                       => Res(Value.True, env.store)
    case False                      => Res(Value.False, env.store)
    case Integer(v)                 => Res(Value.Int(v), env.store)
    case Unit                       => Res(Value.Unit, env.store)
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
  val parsed = parse("""new { root =>
    val x: Int = 0;
    macro m(): Int => Int = `f';
    val res: Int = {
      val f: Int => Int = (x: Int) => x;
      val z: Int => Int = m;
      z 1
    }
  }""")
  println(parsed.map { t => s"parsed:\n$t\n" }.getOrElse(parsed.toString))

  val attributed = attribute.term(parsed.get)
  println(s"attributed:\n$attributed\n")

  val expanded = expand.term(attributed)
  println(s"expanded:\n$expanded\n")

  val value = eval.term(expanded)
  println(s"evaluated:\n$value")
}
