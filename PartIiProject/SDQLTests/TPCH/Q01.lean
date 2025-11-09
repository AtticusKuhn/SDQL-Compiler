import PartIiProject.SyntaxSDQL
import PartIiProject.SurfaceCore

/-
TPCH Q1 (setup only):

Original sdql-rs program (sdql-rs/progs/tpch/1.sdql):

let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

let l_h =
  sum(<i,_> <- range(lineitem.size))
    if(lineitem.l_shipdate(i) <= date(19980902)) then
      { < returnflag = lineitem.l_returnflag(i), linestatus = lineitem.l_linestatus(i) > ->
         <
           l_quantity_sum = lineitem.l_quantity(i),
           l_extendedprice_sum = lineitem.l_extendedprice(i),
           agg1 = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)),
           agg2 = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) * (1.0 + lineitem.l_tax(i)),
           mult = 1
         >
      }

sum(<k,v> <- l_h)
  { unique(concat(k,v)) -> true }

Notes for this Lean setup:
- load is modeled via free variables (see `fvQ01` and `freeVariable`).
- We split the loaded record into multiple free variables, one per field,
  so we can use the `[SDQL| ... ]` DSL without named-field projection.
- Types not yet available in the surface (real/date) are temporarily modeled as int.
- `varchar(n)` is modeled as int for now because lookup requires an additive structure.
- Unsupported constructs in the EDSL (range, date literals, comparisons, unique, concat,
  subtraction, floating-point literals) are left as TODOs; we provide placeholders so the
  term compiles and can be elaborated later.
-/

namespace PartIiProject
namespace SDQLTests
namespace TPCH

open PartIiProject

/- Free-variable layout for Q01.
   We model each referenced field and a range set as an input.
   0: range_over_size        : dict int bool            -- models range(lineitem.size)
   1: l_returnflag           : dict int int             -- was varchar(1)
   2: l_linestatus           : dict int int             -- was varchar(1)
   3: l_quantity             : dict int int             -- was real
   4: l_extendedprice        : dict int int             -- was real
   5: l_discount             : dict int int             -- was real (unused placeholder)
   6: l_tax                  : dict int int             -- was real (unused placeholder)
   7: l_shipdate             : dict int int             -- was date (unused placeholder)
   We can extend this list later if we use more fields or keep them grouped.
-/
abbrev fvQ01 : Fin 8 → SurfaceTy :=
  fun i =>
    match i.val with
    | 0 => .dict .int .bool
    | 1 => .dict .int .int
    | 2 => .dict .int .int
    | 3 => .dict .int .int
    | 4 => .dict .int .int
    | 5 => .dict .int .int
    | 6 => .dict .int .int
    | 7 => .dict .int .int
    | _ => .int -- unreachable

/- Skeleton for l_h aggregation using the EDSL.
   TODOs left where the surface syntax or types are not yet supported.

   We approximate the guard `lineitem.l_shipdate(i) <= date(19980902)` as `true` for now.
   We approximate `agg1` and `agg2` with simple scaled terms as subtraction and FP are missing.
-/
unsafe def q01_l_h : STerm fvQ01 (SurfaceTy.dict
    (SurfaceTy.record [("linestatus", .int), ("returnflag", .int)])
    (SurfaceTy.record [("agg1", .int), ("agg2", .int), ("l_extendedprice_sum", .int), ("l_quantity_sum", .int), ("mult", .int)])) :=
  -- Bind free variables into names the DSL can refer to
  (fun {rep} =>
    STerm'.letin (STerm'.freeVariable (⟨0, by decide⟩)) (fun range_over_size =>
    STerm'.letin (STerm'.freeVariable (⟨1, by decide⟩)) (fun l_returnflag =>
    STerm'.letin (STerm'.freeVariable (⟨2, by decide⟩)) (fun l_linestatus =>
    STerm'.letin (STerm'.freeVariable (⟨3, by decide⟩)) (fun l_quantity =>
    STerm'.letin (STerm'.freeVariable (⟨4, by decide⟩)) (fun l_extendedprice =>
    -- placeholders for discount/tax/shipdate; currently unused in the placeholder body
    STerm'.letin (STerm'.freeVariable (⟨5, by decide⟩)) (fun l_discount =>
    STerm'.letin (STerm'.freeVariable (⟨6, by decide⟩)) (fun l_tax =>
    STerm'.letin (STerm'.freeVariable (⟨7, by decide⟩)) (fun l_shipdate =>
      -- Body in the SDQL DSL. Guard and FP ops are TODO; we drop the guard for now.
      [SDQL|
        sum( <i, _> in range_over_size )
          { < returnflag = l_returnflag(i), linestatus = l_linestatus(i) > ->
             <
               l_quantity_sum = l_quantity(i),
               l_extendedprice_sum = l_extendedprice(i),
               agg1 = l_extendedprice(i) * { int } 1,
               agg2 = l_extendedprice(i) * { int } 1,
               mult = 1
             >
          }
      ]
    ))))))))

/- TODO: final projection step
   The original program does:
     sum(<k,v> <- l_h) { unique(concat(k,v)) -> true }
   which requires `unique`, `concat`, and set semantics.
   We'll add this once the necessary surface constructs are available.
-/
-- Placeholder just exposing the partial result for now
unsafe def q01_partial := q01_l_h

end TPCH
end SDQLTests
end PartIiProject
