#import "@preview/simplebnf:0.1.1": *
#import "@preview/adaptive-dots:0.1.0": adaptive-dots
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#let mathpar(
  numbering: auto,
  row-gutter: 1.2em, // can be set to 'auto'
  column-gutter: 2.5em,
  ..children
) = layout(bounds => {
  // Resolve parameters
  let numbering = if numbering == auto { math.equation.numbering } else { numbering }
  let row-gutter = if row-gutter == auto { par.leading } else { row-gutter.to-absolute() }
  let column-gutter = column-gutter.to-absolute()
  let children = children.pos().map(child => [#child])

  // Spread children into lines
  let widths = children.map(child => measure(child).width)
  let lines = ((children: (), remaining: bounds.width),)
  for (child, width) in children.zip(widths) {
    if (
      child.func() == linebreak or
      (lines.last().remaining - width) / (lines.last().children.len() + 2) < column-gutter
    ){
      lines.push((children: (), remaining: bounds.width))
    }

    if child.func() != linebreak {
      lines.last().children.push(child)
      lines.last().remaining -= width
    }
  }

  // Layout children in math mode for baseline alignment
  par(leading: row-gutter, math.equation(numbering: numbering, block: true,
    for (i, line) in lines.enumerate() {
      let space = h(line.remaining / (line.children.len() + 1))
      par(leading: par.leading, space + line.children.join(space) + space)
      if i != lines.len() - 1 { linebreak() }
    }
  ))
})

= Cover page

= Declaration of originality

= Proforma

= Table of contents
#outline()

= Chapter 1: Introduction

== Motivation

== SDQL
=== Syntax and Typing Rules of SDQL
#bnf(
  Prod(
    $b$,
    annot: "builtin function",
    {
      Or[||][_or_]
      Or[&&][_and_]
      Or[=][_equals_]
      Or[<=][_less than or equal to_]
      Or[<][_less than_]
      Or[-][_subtraction_]
      Or[/][_division_]
      Or[endsWith][_string ends with_]
      Or[startsWith][_string starts with_]
      Or[contains][_string contains_]
      Or[firstIndex][_first index in string_]
      Or[subString][_substring of a string_]
      Or[dom][_domain of a dictionary_]
      Or[range][_The range $1 ... n$_]
      Or[size][_The size of a dictionary_]
      Or[date][_a date literal_]
      Or[year][_the year of a date_]
      Or[concat][_concatenate two records_]
    },
  ),
)

#bnf(
  Prod(
    $t$,
    annot: "Type",
    {
      Or[BB][_BBean_]
      Or[real][_real number_]
      Or[date][_date_]
      Or[$\{t_1 arrow t_2}$][_dictionary_]
      Or[\<$n_1: t_1, n_2: t_2, ..., n_m : t_m$>][_record_]
      Or[string][_string_]
      Or[int][_int_]
      Or[maxProduct][_max product_]
    },
  ),
)


#bnf(
  Prod(
    $e$,
    annot: "Expr",
    {
      Or[$x$][_variable_]
      Or[$i$][_integer literal_]
      Or[$r$][_real literal_]
      Or[$b$][_BBean literal_]
      Or[$s$][_string literal_]
      Or[$<n_1 = e_1, n_2 = e_2, \ldots, n_m = e_m>$][_record literal_]
      Or[$\{n_1 = e_1, n_2 = e_2, \ldots, n_m = e_m\}$][_dictionary literal_]
      Or[$e_1(e_2)$][_dictionary lookup_]
      Or[not(e)][_not_]
      Or[if $e_1$ then $e_2$ else $e_3$][_if-then-else_]
      Or[let x = $e_1$ in $e_2$][_let-in_]
      Or[$e_1 + e_2$][_addition_]
      Or[$e_1 * e_2$][_multiplication_]
      Or[$e_1 *s e_2$][_semi-ring multiplication_]
      Or[closure(e)][_closure_]
      Or[promote[T](e)][_type promotion_]
      Or[sum(\<k,v> in $e_1$) $e_2$][_sum_]
      Or[$e.i$][_projection_]
      Or[$b(e)$][_builtin function_]
    },
  ),
)
#let ty_var = prooftree(rule(
  name: [T-Var],
  $in\ A\ Gamma$,
  $Gamma tack x : A$,
))

#let ty_const_int = prooftree(rule(
  name: [T-Int],
  $Gamma tack i : #int$,
))

#let ty_const_real = prooftree(rule(
  name: [T-Real],
    $Gamma tack r : RR$,
))

#let ty_const_BB = prooftree(rule(
  name: [T-BB],
    $Gamma tack b : BB$,
))

#let ty_const_string = prooftree(rule(
  name: [T-String],
  $Gamma tack s : "string"$,
))

#let ty_record = prooftree(rule(
  name: [T-Record],
  $Gamma tack e_1 : t_1$,
  $dots$,
  $Gamma tack e_n : t_n$,
  $Gamma tack <e_1, \ldots, e_n> : <t_1, \ldots, t_n>$,
))

#let ty_empty_dict = prooftree(rule(
  name: [T-EmptyDict],
  $Gamma tack {} : \{t_1 arrow t_2\}$,
))

#let ty_dict_insert = prooftree(rule(
  name: [T-DictInsert],
  $Gamma tack k : t_1$,
  $Gamma tack v : t_2$,
  $Gamma tack d : \{t_1 arrow t_2\}$,
  $Gamma tack \{k -> v\} ++ d : \{t_1 arrow t_2\}$,
))

#let ty_lookup = prooftree(rule(
  name: [T-Lookup],
  $"AddM"\ t_2$,
  $Gamma tack d : \{t_1 arrow t_2\}$,
  $Gamma tack k : t_1$,
  $Gamma tack d(k) : t_2$,
))

#let ty_not = prooftree(rule(
  name: [T-Not],
  $Gamma tack e : BB$,
  $Gamma tack "not"(e) : BB$,
))

#let ty_ite = prooftree(rule(
  name: [T-If],
  $Gamma tack e_1 : BB$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_3 : t$,
  $Gamma tack "if" e_1 "then" e_2 "else" e_3 : t$,
))

#let ty_letin = prooftree(rule(
  name: [T-Let],
  $Gamma tack e_1 : t_1$,
  $Gamma, t_1 tack e_2 : t_2$,
  $Gamma tack "let" x = e_1 "in" e_2 : t_2$,
))

#let ty_add = prooftree(rule(
  name: [T-Add],
  $"AddM"\ t$,
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 + e_2 : t$,
))

#let ty_mul = prooftree(rule(
  name: [T-Mul],
  $"ScaleM"\ s\ t_1$,
  $"ScaleM"\ s\ t_2$,
  $"has_tensor"\ t_1\ t_2\ t_3$,
  $Gamma tack e_1 : t_1$,
  $Gamma tack e_2 : t_2$,
  $Gamma tack e_1 * e_2 : t_3$,
))

#let ty_semiring_mul = prooftree(rule(
  name: [T-SemiringMul],
  $"HasMul"\ t$,
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 *s e_2 : t$,
))

#let ty_closure = prooftree(rule(
  name: [T-Closure],
  $"HasClosure"\ t$,
  $Gamma tack e : t$,
  $Gamma tack "closure"(e) : t$,
))

#let ty_promote = prooftree(rule(
  name: [T-Promote],
  $Gamma tack e : t_1$,
  $Gamma tack "promote"[t_2](e) : t_2$,
))

#let ty_sum = prooftree(rule(
  name: [T-Sum],
  $"AddM"\ t$,
  $Gamma tack d : \{t_1 arrow t_2\}$,
  $Gamma, t_1, t_2 tack e : t$,
  $Gamma tack "sum"(<k, v> "in" d) e : t$,
))

#let ty_proj = prooftree(rule(
  name: [T-Proj],
  $"has_proj"\ <t_1, \ldots, t_n>\ i\ t$,
  $Gamma tack r : <t_1, \ldots, t_n>$,
  $Gamma tack r.i : t$,
))

#let ty_builtin = prooftree(rule(
  name: [T-Builtin],
  $f : a => b$,
  $Gamma tack e : a$,
  $Gamma tack f(e) : b$,
))

#align(center, rule-set(
  ty_var,
  ty_const_int,
  ty_const_real,
  ty_const_BB,
  ty_const_string,
  ty_record,
  ty_empty_dict,
  ty_dict_insert,
  ty_lookup,
  ty_not,
  ty_ite,
  ty_letin,
  ty_add,
  ty_mul,
  ty_semiring_mul,
  ty_closure,
  ty_promote,
  ty_sum,
  ty_proj,
  ty_builtin,
))
== Previous Work on SDQL

= Chapter 2: Preparation

= Chapter 3: Implementation

= Chapter 4: Evaluation

= Chapter 5: Conclusions

= Bibliography

= Appendices

= Project Proposal
