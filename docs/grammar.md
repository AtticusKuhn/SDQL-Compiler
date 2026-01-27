# SDQL Grammar (BNF)

This document describes the **surface syntax** currently accepted by the Lean SDQL DSL (`PartIiProject/SyntaxSDQL.lean`),
which elaborates into the parser-output AST `LoadTerm'` (`PartIiProject/Untyped/LoadTerm.lean`).

SDQL is (currently) an **expression language**: a “program” is typically just one expression, possibly containing
`load[...]("path")` nodes that refer to external tables.

## Lexical elements

The grammar below treats the following as atomic tokens:

- `<int>`: a (non-negative) integer literal. Negative integers are written using subtraction, e.g. `0 - 1`.
- `<real>`: a floating/scientific literal (e.g. `1.0`, `1e-3`).
- `<string>`: a double-quoted string literal.
- `<ident>`: an identifier. In the current Lean parser, identifiers follow Lean’s `ident` rules, and additionally SDQL
  allows `_` as an identifier (Lean reserves `_` for holes). The identifier `size` is also allowed as a variable name.

Keywords (e.g. `let`, `if`, `sum`, `load`, `promote`) are reserved and are written literally in the grammar as terminals.

## Types

```
<ty>         ::= "int"
               | "bool"
               | "real"
               | "max_prod"
               | "date"
               | "string"
               | "varchar" "(" <int> ")"
               | "{" <ty> "->" <ty> "}"              -- dictionary type
               | "@vec" "{" <ty> "->" <ty> "}"       -- parsed as a dictionary type
               | "<" <tyFieldsOpt> ">"               -- record type

<tyFieldsOpt>::= <tyFields> | ε
<tyFields>   ::= <tyField> | <tyField> "," <tyFields>
<tyField>    ::= <ident> ":" <ty>
```

## Expressions

### High-level forms (lowest precedence)

```
<expr>       ::= <letExpr>
               | <ifExpr>
               | <sumExpr>
               | <orExpr>

<letExpr>    ::= "let" <ident> "=" <expr> "in" <expr>

<ifExpr>     ::= "if" <expr> "then" <expr> "else" <expr>
               | "if" <expr> "then" <expr>

<sumExpr>    ::= "sum" "(" "<" <ident> "," <ident> ">" <sumSrc> <expr> ")" <expr>
<sumSrc>     ::= "in" | "<-"
```

`sum(<k, v> in d) body` iterates over dictionary `d`, binding key `k` and value `v` in `body`.

### Boolean, comparison, and arithmetic operators

Operators are left-associative, with precedence (tightest → loosest):

1. postfix lookup/projection: `e(k)`, `e.field`
2. multiplication/division: `*`, `*s`, `*{S}`, `/`
3. addition/subtraction: `+`, `-`
4. comparisons: `==`, `<=`, `<`
5. boolean AND/OR: `&&`, `||`

The grammar below encodes that precedence:

```
<orExpr>     ::= <andExpr> <orTail>
<orTail>     ::= "||" <andExpr> <orTail> | ε

<andExpr>    ::= <cmpExpr> <andTail>
<andTail>    ::= "&&" <cmpExpr> <andTail> | ε

<cmpExpr>    ::= <addExpr> <cmpTail>
<cmpTail>    ::= "==" <addExpr> <cmpTail>
               | "<=" <addExpr> <cmpTail>
               | "<"  <addExpr> <cmpTail>
               | ε

<addExpr>    ::= <mulExpr> <addTail>
<addTail>    ::= "+" <mulExpr> <addTail>
               | "-" <mulExpr> <addTail>
               | ε

<mulExpr>    ::= <unaryExpr> <mulTail>
<mulTail>    ::= <mulOp> <unaryExpr> <mulTail> | ε

<mulOp>      ::= "*" | "/" | "*{" <scalarTy> "}"
               | "*s"
<scalarTy>   ::= "int" | "bool" | "real" | "max_prod"

<unaryExpr>  ::= "not" <unaryExpr> | <postfixExpr>
```

`*{S}` optionally annotates multiplication with an explicit scalar semiring `S` to disambiguate; plain `*` leaves the
scalar implicit (to be inferred later).

### Postfix lookup and projection

```
<postfixExpr>::= <atom> <postfixTail>

<postfixTail>::= "(" <expr> ")" <postfixTail>     -- dictionary lookup: d(k)
               | "." <ident> <postfixTail>        -- record projection: r.field
               | ε
```

### Atoms, literals, and built-in forms

```
<atom>       ::= <int>
               | <real>
               | <string>
               | "true"
               | "false"
               | <ident>
               | "(" <expr> ")"
               | <recordLit>
               | <dictLit>
               | <typedEmptyDict>
               | <closure>
               | <promote>
               | <load>
               | <builtin>

<recordLit>  ::= "<" <expr> "," <expr> ">"
               | "<" <expr> "," <expr> "," <expr> ">"
               | "<" <namedFieldsOpt> ">"

<namedFieldsOpt>
             ::= <namedFields> | ε
<namedFields>::= <namedField> | <namedField> "," <namedFields>
<namedField> ::= <ident> "=" <expr>

<dictLit>    ::= "{" <dictEntriesOpt> "}"
<dictEntriesOpt>
             ::= <dictEntries> | ε
<dictEntries>::= <dictEntry> | <dictEntry> "," <dictEntries>
<dictEntry>  ::= <expr> "->" <expr>

<typedEmptyDict>
             ::= "{" "}" "_" "{" <ty> "," <ty> "}"     -- {}_{Tdom, Trange}

<promote>    ::= "promote" "[" <ty> "]" "(" <expr> ")"
<closure>    ::= "closure" "(" <expr> ")"

<load>       ::= "load" "[" <ty> "]" "(" <string> ")"
```

Built-ins (as currently parsed):

```
<builtin>    ::= "dom" "(" <expr> ")"
               | "range" "(" <expr> ")"
               | "size" "(" <expr> ")"
               | "endsWith" "(" <expr> "," <expr> ")"
               | "StrStartsWith" "(" <expr> "," <expr> ")"
               | "StrContains" "(" <expr> "," <expr> ")"
               | "FirstIndex" "(" <expr> "," <expr> ")"
               | "LastIndex" "(" <expr> "," <expr> ")"
               | "SubString" "(" <expr> "," <expr> "," <expr> ")"
               | "date" "(" <int> ")"
               | "year" "(" <expr> ")"
               | "concat" "(" <expr> "," <expr> ")"
               | "unique" "(" <expr> ")"               -- currently parses as identity
```

## Notes

- `{ ... }` dictionary literals are syntactic sugar for a chain of inserts over an (unannotated) empty dictionary; the
  type checker will usually need contextual type information for `{}` unless you use `{}_{Tdom, Trange}`.
- Record literals support either positional fields (`<e1,e2>`, `<e1,e2,e3>`) or named fields (`<a=e1, b=e2, ...>`).
- The surface parser accepts dotted identifiers like `r.a.b` as sugar for nested projections.
