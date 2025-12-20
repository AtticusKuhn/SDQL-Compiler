import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/10.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- 
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }
-- 
-- let c_h =
--   sum(<i,_> <- range(customer.size))
--     {
--       unique(customer.c_custkey(i)) ->
--       <
--         _ = customer.c_custkey(i),
--         _ = customer.c_name(i),
--         _ = customer.c_acctbal(i),
--         _ = customer.c_address(i),
--         _ = customer.c_nationkey(i),
--         _ = customer.c_phone(i),
--         _ = customer.c_comment(i)
--       >
--     }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     if(
--          (date(19931001)  <= orders.o_orderdate(i))
--          && (orders.o_orderdate(i) < date(19940101))
--          && (dom(c_h)(orders.o_custkey(i)))
--        ) then
--       {
--         unique(orders.o_orderkey(i)) ->
--         <
--           c_custkey =c_h(orders.o_custkey(i))(0),
--           c_name =c_h(orders.o_custkey(i))(1),
--           c_acctbal =c_h(orders.o_custkey(i))(2),
--           c_address =c_h(orders.o_custkey(i))(3),
--           c_phone =c_h(orders.o_custkey(i))(5),
--           c_comment =c_h(orders.o_custkey(i))(6),
--           n_name = n_h((c_h(orders.o_custkey(i)))(4))(0)
--         >
--       }
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if((lineitem.l_returnflag(i) == "R") && (dom(o_h)(lineitem.l_orderkey(i)))) then
--       {
--         <
--           c_custkey = o_h(lineitem.l_orderkey(i))(0),
--           c_name = o_h(lineitem.l_orderkey(i))(1),
--           c_acctbal = o_h(lineitem.l_orderkey(i))(2),
--           n_name = o_h(lineitem.l_orderkey(i))(6),
--           c_address = o_h(lineitem.l_orderkey(i))(3),
--           c_phone = o_h(lineitem.l_orderkey(i))(4),
--           c_comment = o_h(lineitem.l_orderkey(i))(5)
--         >
--         -> lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
--       }
-- 
-- sum(<k,v> <- l_h)
--   {
--     unique(<
--       c_custkey = k.c_custkey,
--       c_name = k.c_name,
--       revenue = v,
--       c_acctbal = k.c_acctbal,
--       n_name = k.n_name,
--       c_phone = k.c_phone,
--       c_address = k.c_address,
--       c_comment = k.c_comment
--     >)
--     -> true
--   }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q10_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q10 : SProg :=
  [SDQLProg { int }|
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")

    let n_h =
      sum(<i,_> <- range(nation.size))
        { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }

    let c_h =
      sum(<i,_> <- range(customer.size))
        {
          unique(customer.c_custkey(i)) ->
          <
            _ = customer.c_custkey(i),
            _ = customer.c_name(i),
            _ = customer.c_acctbal(i),
            _ = customer.c_address(i),
            _ = customer.c_nationkey(i),
            _ = customer.c_phone(i),
            _ = customer.c_comment(i)
          >
        }

    let o_h =
      sum(<i,_> <- range(orders.size))
        if(
             (date(19931001)  <= orders.o_orderdate(i))
             && (orders.o_orderdate(i) < date(19940101))
             && (dom(c_h)(orders.o_custkey(i)))
           ) then
          {
            unique(orders.o_orderkey(i)) ->
            <
              c_custkey =c_h(orders.o_custkey(i))(0),
              c_name =c_h(orders.o_custkey(i))(1),
              c_acctbal =c_h(orders.o_custkey(i))(2),
              c_address =c_h(orders.o_custkey(i))(3),
              c_phone =c_h(orders.o_custkey(i))(5),
              c_comment =c_h(orders.o_custkey(i))(6),
              n_name = n_h((c_h(orders.o_custkey(i)))(4))(0)
            >
          }

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if((lineitem.l_returnflag(i) == "R") && (dom(o_h)(lineitem.l_orderkey(i)))) then
          {
            <
              c_custkey = o_h(lineitem.l_orderkey(i))(0),
              c_name = o_h(lineitem.l_orderkey(i))(1),
              c_acctbal = o_h(lineitem.l_orderkey(i))(2),
              n_name = o_h(lineitem.l_orderkey(i))(6),
              c_address = o_h(lineitem.l_orderkey(i))(3),
              c_phone = o_h(lineitem.l_orderkey(i))(4),
              c_comment = o_h(lineitem.l_orderkey(i))(5)
            >
            -> lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
          }

    sum(<k,v> <- l_h)
      {
        unique(<
          c_custkey = k.c_custkey,
          c_name = k.c_name,
          revenue = v,
          c_acctbal = k.c_acctbal,
          n_name = k.n_name,
          c_phone = k.c_phone,
          c_address = k.c_address,
          c_comment = k.c_comment
        >)
        -> true
      }
  ]
-/

end Tests.TPCH
