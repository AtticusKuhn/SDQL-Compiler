import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/18.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     { lineitem.l_orderkey(i) -> lineitem.l_quantity(i) }
-- 
-- let orderkeys =
--   sum(<l_orderkey,l_quantity> <- l_h)
--     if(300.0 < l_quantity) then
--       { unique(l_orderkey) -> true }
-- 
-- let custkey_to_name =
--   sum(<i,_> <- range(customer.size))
--     { unique(customer.c_custkey(i)) -> < _ = customer.c_name(i) > }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if((dom(orderkeys)(orders.o_orderkey(i))) && (dom(custkey_to_name)(orders.o_custkey(i)))) then
--       {
--         unique(orders.o_orderkey(i)) ->
--         <
--           name = custkey_to_name(orders.o_custkey(i))(0),
--           custkey = orders.o_custkey(i),
--           orderkey = orders.o_orderkey(i),
--           orderdate = orders.o_orderdate(i),
--           totalprice = orders.o_totalprice(i)
--         >
--       }
-- 
-- let result_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(dom(o_h)(lineitem.l_orderkey(i))) then
--       { o_h(lineitem.l_orderkey(i)) -> < _ = lineitem.l_quantity(i) > }
-- 
-- sum(<k,v> <- result_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q18_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q18 : SProg :=
  [SDQLProg { int }|
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        { lineitem.l_orderkey(i) -> lineitem.l_quantity(i) }

    let orderkeys =
      sum(<l_orderkey,l_quantity> <- l_h)
        if(300.0 < l_quantity) then
          { unique(l_orderkey) -> true }

    let custkey_to_name =
      sum(<i,_> <- range(customer.size))
        { unique(customer.c_custkey(i)) -> < _ = customer.c_name(i) > }

    let o_h =
      sum(<i,_> <- range(orders.size))
        if((dom(orderkeys)(orders.o_orderkey(i))) && (dom(custkey_to_name)(orders.o_custkey(i)))) then
          {
            unique(orders.o_orderkey(i)) ->
            <
              name = custkey_to_name(orders.o_custkey(i))(0),
              custkey = orders.o_custkey(i),
              orderkey = orders.o_orderkey(i),
              orderdate = orders.o_orderdate(i),
              totalprice = orders.o_totalprice(i)
            >
          }

    let result_h =
      sum(<i,_> <- range(lineitem.size))
        if(dom(o_h)(lineitem.l_orderkey(i))) then
          { o_h(lineitem.l_orderkey(i)) -> < _ = lineitem.l_quantity(i) > }

    sum(<k,v> <- result_h)
      { unique(concat(k,v)) -> true }
  ]
-/

end Tests.TPCH
