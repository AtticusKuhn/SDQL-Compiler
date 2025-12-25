import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/5.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl")
--
-- let r_h =
--   sum(<i,_> <- range(region.size))
--     if(region.r_name(i) == "ASIA") then
--       { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > }
--
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     if(dom(r_h)(nation.n_regionkey(i))) then
--       { unique(nation.n_nationkey(i)) -> nation.n_name(i) }
--
-- let c_h =
--   sum(<i,_> <- range(customer.size))
--     if(dom(n_h)(customer.c_nationkey(i))) then
--       { unique(customer.c_custkey(i)) -> < _ =n_h(customer.c_nationkey(i)), _ = customer.c_nationkey(i) > }
--
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if(
--         (orders.o_orderdate(i) < date(19950101))
--         && (date(19940101) <= orders.o_orderdate(i))
--         && (dom(c_h)(orders.o_custkey(i)))
--       ) then
--       { unique(orders.o_orderkey(i)) -> < _ = c_h(orders.o_custkey(i))(0), _ = c_h(orders.o_custkey(i))(1) > }
--
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     { unique(< _ = supplier.s_suppkey(i), _ = supplier.s_nationkey(i) >) -> true }
--
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--         (dom(o_h)(lineitem.l_orderkey(i)))
--         && (dom(s_h)(< _ = lineitem.l_suppkey(i), _ = o_h(lineitem.l_orderkey(i))(1) >))
--       ) then
--       { o_h(lineitem.l_orderkey(i))(0) -> lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) }
--
-- sum(<k,v> <- l_h)
--   { unique(< _ = k, _ = v >) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q05_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)

unsafe def Q05 : SProg2 :=
  [SDQLProg2 { { < _1 : string, _2 : real> -> bool } }|
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl") in
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl") in
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl") in
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl") in
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl") in
    let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl") in

    let r_h =
      sum(<i,_> <- range(region.size))
        if(region.r_name(i) == "ASIA") then
          { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > } in

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(dom(r_h)(nation.n_regionkey(i))) then
          { unique(nation.n_nationkey(i)) -> nation.n_name(i) } in

    let c_h =
      sum(<i,_> <- range(customer.size))
        if(dom(n_h)(customer.c_nationkey(i))) then
          { unique(customer.c_custkey(i)) -> < n_h(customer.c_nationkey(i)),customer.c_nationkey(i) > } in

    let o_h =
      sum(<i,_> <- range(orders.size))
        if(
            (orders.o_orderdate(i) < date(19950101))
            && (date(19940101) <= orders.o_orderdate(i))
            && (dom(c_h)(orders.o_custkey(i)))
          ) then
          { unique(orders.o_orderkey(i)) -> <  c_h(orders.o_custkey(i))._1,  c_h(orders.o_custkey(i))._2 > } in

    let s_h =
      sum(<i,_> <- range(supplier.size))
        { unique(<  supplier.s_suppkey(i), supplier.s_nationkey(i) >) -> true } in

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
            (dom(o_h)(lineitem.l_orderkey(i)))
            && (dom(s_h)(< lineitem.l_suppkey(i),  o_h(lineitem.l_orderkey(i))(1) >))
          ) then
          { o_h(lineitem.l_orderkey(i))(0) -> lineitem.l_extendedprice(i) *{real} (1.0 - lineitem.l_discount(i)) } in

    sum(<k,v> <- l_h)
      { unique(<k, v >) -> true }
  ]


end Tests.TPCH
