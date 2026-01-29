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
      Or[bool][_boolean_]
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
      Or[$b$][_boolean literal_]
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
#let variable = prooftree(rule(
  name: [Variable],
  $Gamma, x : A tack x : A$,
))
#let abstraction = prooftree(rule(
  name: [Abstraction],
  $Gamma, x: A tack P : B$,
  $Gamma tack lambda x . P : A => B$,
))

#let application = prooftree(rule(
  name: [Application],
  $Gamma tack P : A => B$,
  $Delta tack Q : B$,
  $Gamma, Delta tack P Q : B$,
))

#let weakening = prooftree(rule(
  name: [Weakening],
  $Gamma tack P : B$,
  $Gamma, x : A tack P : B$,
))

#let contraction = prooftree(rule(
  label: [Contraction],
  $Gamma, x : A, y : A tack P : B$,
  $Gamma, z : A tack P[x, y <- z]: B$,
))

#let exchange = prooftree(rule(
  label: [Exchange],
  $Gamma, x : A, y: B, Delta tack P : B$,
  $Gamma, y : B, x: A, Delta tack P : B$,
))

#align(center, rule-set(
  variable,
  abstraction,
  application,
  weakening,
  contraction,
  exchange
))
== Previous Work on SDQL

= Chapter 2: Preparation

= Chapter 3: Implementation

= Chapter 4: Evaluation

= Chapter 5: Conclusions

= Bibliography

= Appendices

= Project Proposal
