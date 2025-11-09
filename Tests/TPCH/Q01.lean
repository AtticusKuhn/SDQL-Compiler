import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/1.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
--
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(lineitem.l_shipdate(i) <= date(19980902)) then
--       { < returnflag = lineitem.l_returnflag(i), linestatus = lineitem.l_linestatus(i) > ->
--          <
--            l_quantity_sum = lineitem.l_quantity(i),
--            l_extendedprice_sum = lineitem.l_extendedprice(i),
--            agg1 = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)),
--            agg2 = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) * (1.0 + lineitem.l_tax(i)),
--            mult = 1
--          >
--       }
--
-- sum(<k,v> <- l_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q01_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)

unsafe def Q01 : SProg :=
  [SDQLProg { int }|
    let lineitem = load[<l_orderkey:  {int -> int}, l_partkey:  {int -> int}, l_suppkey: {int -> int}, l_linenumber:  {int -> int}, l_quantity:  {int -> int}, l_extendedprice:  {int -> int}, l_discount:  {int -> int}, l_tax:  {int -> int}, l_returnflag:  {int -> string}, l_linestatus:  {int -> string}, l_shipdate:  {int -> string}, l_commitdate:  {int -> string}, l_receiptdate:  {int -> string}, l_shipinstruct:  {int -> string}, l_shipmode: {int -> string}, l_comment: {int -> string}, size: int>]("datasets/tpch/lineitem.tbl") in

    let l_h =
      sum(<i,k> in range(lineitem.size))
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
  ]


end Tests.TPCH
