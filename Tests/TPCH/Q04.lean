import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/4.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if((lineitem.l_commitdate(i) < lineitem.l_receiptdate(i))) then
--       @vec(6000001) { lineitem.l_orderkey(i) -> true }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if(
--       (date(19930701) <= orders.o_orderdate(i))
--       && (orders.o_orderdate(i) < date(19931001))
--       && l_h(orders.o_orderkey(i)) == true
--     ) then
--       { orders.o_orderpriority(i) -> 1 }
-- 
-- sum(<k, v> <- o_h)
--   { unique(< _ = k, _ = v >) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q04_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q04 : SProg :=
  [SDQLProg { int }|
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if((lineitem.l_commitdate(i) < lineitem.l_receiptdate(i))) then
          @vec(6000001) { lineitem.l_orderkey(i) -> true }

    let o_h =
      sum(<i,_> <- range(orders.size))
        if(
          (date(19930701) <= orders.o_orderdate(i))
          && (orders.o_orderdate(i) < date(19931001))
          && l_h(orders.o_orderkey(i)) == true
        ) then
          { orders.o_orderpriority(i) -> 1 }

    sum(<k, v> <- o_h)
      { unique(< _ = k, _ = v >) -> true }
  ]
-/

end Tests.TPCH
