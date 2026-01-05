
- The implementation of `concat` in Rust is ugly, need to fix it.
- `sub` currently type `t -> t -> t`, should introduce a typeclass for it.
- Get github workflow to run successfully.
- Make `<` and `<=` and `==` use a typeclass (instead of taking in any type `t`)
- We currently use a bad representation of dates (i.e. YYYYMMDD as an `i64`). This is dumb.
  Missing SDQL features to run the remaining TPCH queries (Q07–Q09, Q11, Q13–Q17, Q20–Q22) without rewriting them:

  - String extensions StrStartsWith, StrContains, FirstIndex, LastIndex, SubString (Q08/Q14/Q16/Q20/Q22, Q09, Q13/Q16, Q22).
  - Scalar promotion / promote[max_prod] (Q15).
Q15 is tiny-only (SF=0.01 currently diverges due to missing
    promote[max_prod]/max-semirings).
- change how `Rust.Expr` is represented to use DeBruijn indexing instead of string for variables
- get rid of ugly `A *{Type} B` syntax
- Get rid of ugly `<_1 =..., _2 = ...>` syntax. Just replace this with `<..., ....>`
- Make script to check performance of testcases.
