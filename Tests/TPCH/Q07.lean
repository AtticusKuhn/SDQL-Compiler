import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/7.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
--
-- let nationkey_to_name =
--   sum(<i,_> <- range(nation.size))
--     if((nation.n_name(i) == "FRANCE") || (nation.n_name(i) == "GERMANY")) then
--       { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }
--
-- let custkey_to_name =
--   sum(<i,_> <- range(customer.size))
--     if(dom(nationkey_to_name)(customer.c_nationkey(i))) then
--       { unique(customer.c_custkey(i)) -> nationkey_to_name(customer.c_nationkey(i))(0) }
--
-- let orderkey_to_name =
--   sum(<i,_> <- range(orders.size))
--     if(dom(custkey_to_name)(orders.o_custkey(i))) then
--       { unique(orders.o_orderkey(i)) -> custkey_to_name(orders.o_custkey(i)) }
--
-- let suppkey_to_name =
--   sum(<i,_> <- range(supplier.size))
--     if(dom(nationkey_to_name)(supplier.s_nationkey(i))) then
--       { unique(supplier.s_suppkey(i)) -> nationkey_to_name(supplier.s_nationkey(i))(0) }
--
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--         (date(19950101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) <= date(19961231)) &&
--         (dom(orderkey_to_name)(lineitem.l_orderkey(i))) && (dom(suppkey_to_name)(lineitem.l_suppkey(i))) &&
--         (
--           ((orderkey_to_name(lineitem.l_orderkey(i)) == "FRANCE") && (suppkey_to_name(lineitem.l_suppkey(i)) == "GERMANY")) ||
--           ((orderkey_to_name(lineitem.l_orderkey(i)) == "GERMANY") && (suppkey_to_name(lineitem.l_suppkey(i)) == "FRANCE"))
--         )
--     ) then
--       {
--         <
--           supp_nation = suppkey_to_name(lineitem.l_suppkey(i)),
--           cust_nation = orderkey_to_name(lineitem.l_orderkey(i)),
--           l_year = ext(`Year`, lineitem.l_shipdate(i))
--         > -> <
--           revenue = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
--         >
--       }
--
-- sum(<k,v> <- l_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q07_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)

unsafe def Q07 : SProg2 :=
  [SDQLProg2 { { < _1 : string, _2 : string, _3 : int, _4 : real > -> bool } }|
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl") in
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl") in
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl") in
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl") in
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl") in

    let nationkey_to_name =
      sum(<i,_> <- range(nation.size))
        if((nation.n_name(i) == "FRANCE") || (nation.n_name(i) == "GERMANY")) then
          { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > } in

    let custkey_to_name =
      sum(<i,_> <- range(customer.size))
        if(dom(nationkey_to_name)(customer.c_nationkey(i))) then
          { unique(customer.c_custkey(i)) -> nationkey_to_name(customer.c_nationkey(i))(0) } in

    let orderkey_to_name =
      sum(<i,_> <- range(orders.size))
        if(dom(custkey_to_name)(orders.o_custkey(i))) then
          { unique(orders.o_orderkey(i)) -> custkey_to_name(orders.o_custkey(i)) } in

    let suppkey_to_name =
      sum(<i,_> <- range(supplier.size))
        if(dom(nationkey_to_name)(supplier.s_nationkey(i))) then
          { unique(supplier.s_suppkey(i)) -> nationkey_to_name(supplier.s_nationkey(i))(0) } in

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
            (date(19950101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) <= date(19961231)) &&
            (dom(orderkey_to_name)(lineitem.l_orderkey(i))) && (dom(suppkey_to_name)(lineitem.l_suppkey(i))) &&
            (
              ((orderkey_to_name(lineitem.l_orderkey(i)) == "FRANCE") && (suppkey_to_name(lineitem.l_suppkey(i)) == "GERMANY")) ||
              ((orderkey_to_name(lineitem.l_orderkey(i)) == "GERMANY") && (suppkey_to_name(lineitem.l_suppkey(i)) == "FRANCE"))
            )
        ) then
          {
            <
              _1 = suppkey_to_name(lineitem.l_suppkey(i)),
              _2 = orderkey_to_name(lineitem.l_orderkey(i)),
              _3 = year(lineitem.l_shipdate(i))
            > -> <
              _4 = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
            >
          } in

    sum(<k,v> <- l_h)
      { unique(concat(k,v)) -> true }
  ]


end Tests.TPCH
