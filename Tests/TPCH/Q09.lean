import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/9.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- 
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }
-- 
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     { unique(supplier.s_suppkey(i)) -> n_h(supplier.s_nationkey(i))(0) }
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if(ext(`StrContains`, part.p_name(i), "green")) then
--       { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }
-- 
-- let ps_h =
--   sum(<i,_> <- range(partsupp.size))
--     if(dom(p_h)(partsupp.ps_partkey(i))) then
--       { unique(< _ = partsupp.ps_partkey(i), _ = partsupp.ps_suppkey(i) >) -> < _ = s_h(partsupp.ps_suppkey(i)), _ = partsupp.ps_supplycost(i) > }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     @vec(6000001) { orders.o_orderkey(i) -> orders.o_orderdate(i) }
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(dom(ps_h)(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)) then
--       {
--         <
--           nation = ps_h(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)(0),
--           o_year = ext(`Year`, o_h(lineitem.l_orderkey(i)))
--         > ->
--          < um_profit = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) - ps_h(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)(1) * lineitem.l_quantity(i) >
--       }
-- 
-- sum(<k,v> <- l_h)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q09_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q09 : SProg :=
  [SDQLProg { int }|
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")

    let n_h =
      sum(<i,_> <- range(nation.size))
        { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }

    let s_h =
      sum(<i,_> <- range(supplier.size))
        { unique(supplier.s_suppkey(i)) -> n_h(supplier.s_nationkey(i))(0) }

    let p_h =
      sum(<i,_> <- range(part.size))
        if(ext(`StrContains`, part.p_name(i), "green")) then
          { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }

    let ps_h =
      sum(<i,_> <- range(partsupp.size))
        if(dom(p_h)(partsupp.ps_partkey(i))) then
          { unique(< _ = partsupp.ps_partkey(i), _ = partsupp.ps_suppkey(i) >) -> < _ = s_h(partsupp.ps_suppkey(i)), _ = partsupp.ps_supplycost(i) > }

    let o_h =
      sum(<i,_> <- range(orders.size))
        @vec(6000001) { orders.o_orderkey(i) -> orders.o_orderdate(i) }

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(dom(ps_h)(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)) then
          {
            <
              nation = ps_h(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)(0),
              o_year = ext(`Year`, o_h(lineitem.l_orderkey(i)))
            > ->
             < um_profit = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) - ps_h(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >)(1) * lineitem.l_quantity(i) >
          }

    sum(<k,v> <- l_h)
      { unique(concat(k,v)) -> true }
  ]
-/

end Tests.TPCH
