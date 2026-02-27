#import "@preview/simplebnf:0.1.1": *
#import "@preview/adaptive-dots:0.1.0": adaptive-dots
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "mathpar.typ": mathpar
#import "@preview/mmdr:0.2.0": mermaid

= Cover page

= Declaration of originality

= Proforma

= Table of contents
#outline()

= Chapter 1: Introduction

== Motivation
Data-science pipelines may contain both data-queries
and linear algebra. PL researchers have designed
DSLs to capture parts of this workflow. Relational
Algebra DSLs model relational data, and linear algebra
frameworks can efficiently compute over tensors. However,
using different DSLs to model each stage introduces
friction at the transition boundry of the data-science
pipeline.

This dissertation implements and extends with new features SDQL, a
DSL based on semi-rings which is flexible enough to
serve as a hybrid DB and also support Linear Algebra
workloads.

SDQL achieves expressivity by modelling data operations
as semi-rings over dictionaries.

A key domain where this is useful is in biomedical data.
The original SDQL paper @asemiring covers this example,
and I would like to try this as well, if I get
the time to do it.

My motivation for undertaking this project was:

+ To test Lean in a real-world compilers project
+ To demonstrate that the unique features of Lean4 as a language, such as dependent types and syntax macros, lead to a cleaner architecture and design of a compiler 
+ To extend the original SDQL paper with semi-rings and closure constructs and apply this to graph problems

@tarjan1981 demonstrates a unified techinque for using semi-rings to solve graph-problems. This approach was referenced, but not implemented, in the original SDQL paper.

== Background on SDQL
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
      Or[lastIndex][_last index in string_]
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
      Or[$<n_1 = e_1, n_2 = e_2, dots, n_m = e_m>$][_record literal_]
      Or[$\{n_1 = e_1, n_2 = e_2, dots, n_m = e_m\}$][_dictionary literal_]
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
  $Gamma tack <e_1, dots, e_n> : <t_1, dots, t_n>$,
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
  $"has_proj"\ <t_1, dots, t_n>\ i\ t$,
  $Gamma tack r : <t_1, dots, t_n>$,
  $Gamma tack r.i : t$,
))

#let ty_or = prooftree(rule(
  name: [T-Or],
  $Gamma tack e_1 : BB$,
  $Gamma tack e_2 : BB$,
  $Gamma tack e_1 || e_2 : BB$,
))

#let ty_and = prooftree(rule(
  name: [T-And],
  $Gamma tack e_1 : BB$,
  $Gamma tack e_2 : BB$,
  $Gamma tack e_1 && e_2 : BB$,
))

#let ty_eq = prooftree(rule(
  name: [T-Eq],
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 = e_2 : BB$,
))

#let ty_leq = prooftree(rule(
  name: [T-Leq],
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 <= e_2 : BB$,
))

#let ty_lt = prooftree(rule(
  name: [T-Lt],
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 < e_2 : BB$,
))

#let ty_sub = prooftree(rule(
  name: [T-Sub],
  $Gamma tack e_1 : t$,
  $Gamma tack e_2 : t$,
  $Gamma tack e_1 - e_2 : t$,
))

#let ty_div = prooftree(rule(
  name: [T-Div],
  $Gamma tack e_1 : RR$,
  $Gamma tack e_2 : RR$,
  $Gamma tack e_1 \/ e_2 : RR$,
))

#let ty_ends_with = prooftree(rule(
  name: [T-EndsWith],
  $Gamma tack e_1 : "string"$,
  $Gamma tack e_2 : "string"$,
  $Gamma tack "endsWith"(e_1, e_2) : BB$,
))

#let ty_starts_with = prooftree(rule(
  name: [T-StartsWith],
  $Gamma tack e_1 : "string"$,
  $Gamma tack e_2 : "string"$,
  $Gamma tack "startsWith"(e_1, e_2) : BB$,
))

#let ty_contains = prooftree(rule(
  name: [T-Contains],
  $Gamma tack e_1 : "string"$,
  $Gamma tack e_2 : "string"$,
  $Gamma tack "contains"(e_1, e_2) : BB$,
))

#let ty_first_index = prooftree(rule(
  name: [T-FirstIndex],
  $Gamma tack e_1 : "string"$,
  $Gamma tack e_2 : "string"$,
  $Gamma tack "firstIndex"(e_1, e_2) : ZZ$,
))

#let ty_last_index = prooftree(rule(
  name: [T-LastIndex],
  $Gamma tack e_1 : "string"$,
  $Gamma tack e_2 : "string"$,
  $Gamma tack "lastIndex"(e_1, e_2) : ZZ$,
))

#let ty_substring = prooftree(rule(
  name: [T-SubString],
  $Gamma tack e : "string"$,
  $Gamma tack i : ZZ$,
  $Gamma tack j : ZZ$,
  $Gamma tack "subString"(e, i, j) : "string"$,
))

#let ty_dom = prooftree(rule(
  name: [T-Dom],
  $Gamma tack d : \{t_1 arrow t_2\}$,
  $Gamma tack "dom"(d) : \{t_1 arrow BB\}$,
))

#let ty_range = prooftree(rule(
  name: [T-Range],
  $Gamma tack e : ZZ$,
  $Gamma tack "range"(e) : \{ZZ arrow BB\}$,
))

#let ty_size = prooftree(rule(
  name: [T-Size],
  $Gamma tack d : \{t_1 arrow t_2\}$,
  $Gamma tack "size"(d) : ZZ$,
))

#let ty_date_lit = prooftree(rule(
  name: [T-DateLit],
  $Gamma tack "date"(n) : "date"$,
))

#let ty_year = prooftree(rule(
  name: [T-Year],
  $Gamma tack e : "date"$,
  $Gamma tack "year"(e) : ZZ$,
))

#let ty_concat = prooftree(rule(
  name: [T-Concat],
  $Gamma tack e_1 : <t_1, dots, t_n>$,
  $Gamma tack e_2 : <s_1, dots, s_m>$,
  $Gamma tack "concat"(e_1, e_2) : <t_1, dots, t_n, s_1, dots, s_m>$,
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
  ty_or,
  ty_and,
  ty_eq,
  ty_leq,
  ty_lt,
  ty_sub,
  ty_div,
  ty_ends_with,
  ty_starts_with,
  ty_contains,
  ty_first_index,
  ty_last_index,
  ty_substring,
  ty_dom,
  ty_range,
  ty_size,
  ty_date_lit,
  ty_year,
  ty_concat,
))

== Previous Work on SDQL
SDQL was introduced by researchers at the University
of Edinburgh in @functionalcollection.

They extended SDQL in @asemiring.

= Chapter 2: Preparation

== Research and Background reading

I began my preparation by doing background reading
on the following papers,

- @functionalcollection for the original introduction to SDQL
- @asemiring for an updated version of SDQL
- @tarjan1981 for background on my algebraic paths extension.

In particular, @tarjan1981 introduces new theory
related to semi-rings and @functionalcollection introduces theory related to linear algebra (in the
section of denotational semantics). I taught myself
this theory in preparation for the project.

== Proposal Refinement

I refined my proposal by consulting with my day-to-day
supervisor, and by proactively reaching out to the
authors of the original SDQL paper.

I was sure to get several rounds of draft and review from my day-to-day supervisor in order to ...

See @email.

From

== Requirements Analysis


I was sure to plan out appropriate software engineering
techniques fitting for this project.

=== The Use of Lean

While not many compilers have been written
in Lean4 yet, I chose it for this project based on
the requirements of the project

+ Lean's features as a functional language make it easy to define transformations over an AST as functions.
+ Lean's dependent types allow ASTs to hold evidence which is used in synthesis.

=== Continuous Integration and Testing



= Chapter 3: Implementation

== Compilation Pipeline

=== High-Level Overview
#mermaid(read("pipeline.mmd"))

=== Intermediate Representations
#mermaid(read("pipeline-irs.mmd"))

=== Elaboration-Time vs Runtime Split
#mermaid(read("pipeline-elab-runtime.mmd"))

=== Optimisation Passes
#mermaid(read("pipeline-optimisations.mmd"))

=== Key Source Files
#mermaid(read("pipeline-source-files.mmd"))





== Theory Semi-Rings in Square Vector Spaces

For any vector space $V$, I will called the vector space
$V times.o V$ square.

Let $V$ be a semi-module over $k$.
Let $B : V * V -> K$ be a bilinear form.

$V times.o V$ is a semi-ring, where multiplication is given by
$ (a times.o b) * (x times.o y) = B(b, x) dot (a times.o y) $.

Let $u = a times.o b$ be an element of $V times.o V$. The Kleene Star is given by:
$ (a times.o b)^* = 1 + B(b, a)^* dot (a times.o b) $

Note that all semi-modules in SDQL have a bilinear form. 
When $V$ is finite-dimensional and $B$ is non-degenerate, the semi-ring $(V times.o V, +, *)$ is isomorphic to the *matrix algebra* $"End"(V) tilde.equiv M_n(k)$:

== The Compilation Pipeline
== Repository Overview

= Chapter 4: Evaluation


== Correctness of compilation testbench (TPC-H Benchmark)

The reference implementation of SDQL implements
the TPC-H benchmark (see @tpch).

I implemented a harness to run both the reference
implementation and the Lean4 implementation on the
TPC-H benchmark at scale factor $S F=0.01$.

In this benchmark are also micro-tests of simple
language constructs to allow for fast iteration and
prototyping.

The output is in <tpch_run>.

== Optimisation Performance tests

== Reference Performance Comparison

== The Use of a Profiler
== Graph Comparison
= Chapter 5: Conclusions

#bibliography("bib.bib")

= Appendices

#figure(
    image("email_to_alex_mascolo.png", width: 80%),
  caption: [Email to authors of the original SDQL implementation],
) <email>

#figure(
read("tpch_run.txt"),
  caption: [TPC-H run output],
) <tpch_run>

= Project Proposal
