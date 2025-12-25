import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/12.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--       ((lineitem.l_shipmode(i) == "MAIL") || (lineitem.l_shipmode(i) == "SHIP"))
--       && (date(19940101) <= lineitem.l_receiptdate(i))
--       && (lineitem.l_receiptdate(i) < date(19950101))
--       && (lineitem.l_shipdate(i) < lineitem.l_commitdate(i))
--       && (lineitem.l_commitdate(i) < lineitem.l_receiptdate(i))
--     ) then
--       { lineitem.l_orderkey(i) -> { lineitem.l_shipmode(i) -> 1 } }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if(dom(l_h)(orders.o_orderkey(i))) then
--       sum(<l_shipmode,c> <- l_h(orders.o_orderkey(i)))
--         {
--           < _ = l_shipmode >
--           -> <
--           high_line_count = if ((orders.o_orderpriority(i) == "1-URGENT") || (orders.o_orderpriority(i) == "2-HIGH")) then c else 0,
--           low_line_count = if ((orders.o_orderpriority(i) != "1-URGENT") && (orders.o_orderpriority(i) != "2-HIGH")) then c else 0
--           >
--         }
-- 
-- sum(<k,v> <- o_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q12_stub : SProg2 := [SDQLProg2 { int }| 0 ]

unsafe def Q12 : SProg2 :=
  [SDQLProg2 { { < _1 : varchar(10), _2 : int, _3 : int > -> bool } }|
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl") in
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl") in

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
          ((lineitem.l_shipmode(i) == "MAIL") || (lineitem.l_shipmode(i) == "SHIP"))
          && (date(19940101) <= lineitem.l_receiptdate(i))
          && (lineitem.l_receiptdate(i) < date(19950101))
          && (lineitem.l_shipdate(i) < lineitem.l_commitdate(i))
          && (lineitem.l_commitdate(i) < lineitem.l_receiptdate(i))
        ) then
          { lineitem.l_orderkey(i) -> { lineitem.l_shipmode(i) -> 1 } } in

    let o_h =
      sum(<i,_> <- range(orders.size))
        if(dom(l_h)(orders.o_orderkey(i))) then
          sum(<l_shipmode,c> <- l_h(orders.o_orderkey(i)))
            {
              < _1 = l_shipmode >
              -> <
                _2 =
                  if ((orders.o_orderpriority(i) == "1-URGENT") || (orders.o_orderpriority(i) == "2-HIGH"))
                  then c else 0,
                _3 =
                  if ((not (orders.o_orderpriority(i) == "1-URGENT")) && (not (orders.o_orderpriority(i) == "2-HIGH")))
                  then c else 0
              >
            } in

    sum(<k,v> <- o_h)
      { unique(concat(k,v)) -> true }
  ]

end Tests.TPCH
