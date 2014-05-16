### List of Scala syntax / Scala parser warts discovered so far

  1. Function parameters can not be annotated
  1. `try expr catch expr` syntax
  1. Package objects can't have annotations
  1. Lambdas can not be disambiguated from self types in templates
  1. Patterns in vals are parsed inconsistently
  1. Awkward meaning of infix patterns: `a infix (b, c)` means `infix(a, b, c)`
  1. `pq"_: F[_]"` is something completely different from `pq"_: F[_ >: lo <: hi]"`
  1. `pq"a[b]"` is a legal pattern
  1. Guess what `pq"a -1"` means
  1. No way to fully qualify things that are in empty package
  1. Vars with default values may not contain patterns
  1. Constr block
  1. `q"def x { case 1 => 2 }"`
  1. `q"trait F[T] <: Sobaka[T] with Balabaka { def bazinga } "`
  1. `*` is ambigious (ident vs seq wildcard) in most contexts
  1. `1 + (y = 2)` is equiv to `1.+(y = 2)` but `1 + (y: _*)` doesn't work
  1. floating scala doc