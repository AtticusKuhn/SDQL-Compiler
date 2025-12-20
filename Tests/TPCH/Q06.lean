import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/6.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- sum(<i,_> <- range(lineitem.size))
--   if((0.05 <= lineitem.l_discount(i)) && (lineitem.l_discount(i) <= 0.07) &&
--       (lineitem.l_quantity(i) < 24.0) && (date(19940101) <= lineitem.l_shipdate(i)) &&
--       (lineitem.l_shipdate(i) < date(19950101))) then
--     lineitem.l_extendedprice(i) * lineitem.l_discount(i)
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q06_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q06 : SProg :=
  [SDQLProg { int }|
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

    sum(<i,_> <- range(lineitem.size))
      if((0.05 <= lineitem.l_discount(i)) && (lineitem.l_discount(i) <= 0.07) &&
          (lineitem.l_quantity(i) < 24.0) && (date(19940101) <= lineitem.l_shipdate(i)) &&
          (lineitem.l_shipdate(i) < date(19950101))) then
        lineitem.l_extendedprice(i) * lineitem.l_discount(i)
  ]
-/

end Tests.TPCH
