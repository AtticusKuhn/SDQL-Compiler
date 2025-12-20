import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/3.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- let c_h =
--   sum(<i,_> <- range(customer.size))
--     if(customer.c_mktsegment(i) == "BUILDING") then
--       { unique(customer.c_custkey(i)) -> < _ = customer.c_custkey(i) > }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if(
--         (orders.o_orderdate(i) < date(19950315))
--         && (dom(c_h)(orders.o_custkey(i)))
--       ) then
--       { unique(orders.o_orderkey(i)) -> < _ = orders.o_orderdate(i), _ = orders.o_shippriority(i) > }
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--         (date(19950315) < lineitem.l_shipdate(i))
--         && (dom(o_h)(lineitem.l_orderkey(i)))
--       ) then
--       {
--         <
--           l_orderkey = lineitem.l_orderkey(i),
--           o_orderdate = o_h(lineitem.l_orderkey(i))(0),
--           o_shippriority = o_h(lineitem.l_orderkey(i))(1)
--         > ->
--          < revenue = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) >
--       }
-- 
-- sum(<k,v> <- l_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q03_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q03 : SProg :=
  [SDQLProg { int }|
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

    let c_h =
      sum(<i,_> <- range(customer.size))
        if(customer.c_mktsegment(i) == "BUILDING") then
          { unique(customer.c_custkey(i)) -> < _ = customer.c_custkey(i) > }

    let o_h =
      sum(<i,_> <- range(orders.size))
        if(
            (orders.o_orderdate(i) < date(19950315))
            && (dom(c_h)(orders.o_custkey(i)))
          ) then
          { unique(orders.o_orderkey(i)) -> < _ = orders.o_orderdate(i), _ = orders.o_shippriority(i) > }

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
            (date(19950315) < lineitem.l_shipdate(i))
            && (dom(o_h)(lineitem.l_orderkey(i)))
          ) then
          {
            <
              l_orderkey = lineitem.l_orderkey(i),
              o_orderdate = o_h(lineitem.l_orderkey(i))(0),
              o_shippriority = o_h(lineitem.l_orderkey(i))(1)
            > ->
             < revenue = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) >
          }

    sum(<k,v> <- l_h)
      { unique(concat(k,v)) -> true }
  ]
-/

end Tests.TPCH
