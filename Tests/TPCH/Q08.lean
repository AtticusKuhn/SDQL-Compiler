import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/8.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl")
-- 
-- let r_h =
--   sum(<i,_> <- range(region.size))
--     if(region.r_name(i) == "AMERICA") then
--       { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > }
-- 
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     if(dom(r_h)(nation.n_regionkey(i))) then
--       { unique(nation.n_nationkey(i)) -> true }
-- 
-- let nationkey_to_name =
--   sum(<i,_> <- range(nation.size))
--     { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }
-- 
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_nationkey(i) > }
-- 
-- let c_h =
--   sum(<i,_> <- range(customer.size))
--     @vec(200001) { customer.c_custkey(i) -> customer.c_nationkey(i) }
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--       if(part.p_type(i) == "ECONOMY ANODIZED STEEL") then
--         { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--       if((date(19950101) <= orders.o_orderdate(i)) && (orders.o_orderdate(i) <= date(19961231))) then
--         { unique(orders.o_orderkey(i)) -> < _ = orders.o_custkey(i), _ = orders.o_orderdate(i) > }
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--       if((dom(p_h)(lineitem.l_partkey(i))) && (dom(o_h)(lineitem.l_orderkey(i))) && (dom(n_h)(c_h(o_h(lineitem.l_orderkey(i))(0))))) then
--         let orderdate = o_h(lineitem.l_orderkey(i))(1)
--         let orderyear = ext(`Year`, orderdate)
--         let volume = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
--         let brazil_volume = if(nationkey_to_name(s_h(lineitem.l_suppkey(i))(0))(0) == "BRAZIL") then volume else 0.0
--         { orderyear -> < _ = brazil_volume, _ = volume > }
-- 
-- sum(<k,v> <- l_h)
--   { unique(< _ = k, _ = v(0) / v(1) >) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q08_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q08 : SProg :=
  [SDQLProg { int }|
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
    let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl")

    let r_h =
      sum(<i,_> <- range(region.size))
        if(region.r_name(i) == "AMERICA") then
          { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > }

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(dom(r_h)(nation.n_regionkey(i))) then
          { unique(nation.n_nationkey(i)) -> true }

    let nationkey_to_name =
      sum(<i,_> <- range(nation.size))
        { unique(nation.n_nationkey(i)) -> < _ = nation.n_name(i) > }

    let s_h =
      sum(<i,_> <- range(supplier.size))
        { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_nationkey(i) > }

    let c_h =
      sum(<i,_> <- range(customer.size))
        @vec(200001) { customer.c_custkey(i) -> customer.c_nationkey(i) }

    let p_h =
      sum(<i,_> <- range(part.size))
          if(part.p_type(i) == "ECONOMY ANODIZED STEEL") then
            { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }

    let o_h =
      sum(<i,_> <- range(orders.size))
          if((date(19950101) <= orders.o_orderdate(i)) && (orders.o_orderdate(i) <= date(19961231))) then
            { unique(orders.o_orderkey(i)) -> < _ = orders.o_custkey(i), _ = orders.o_orderdate(i) > }

    let l_h =
      sum(<i,_> <- range(lineitem.size))
          if((dom(p_h)(lineitem.l_partkey(i))) && (dom(o_h)(lineitem.l_orderkey(i))) && (dom(n_h)(c_h(o_h(lineitem.l_orderkey(i))(0))))) then
            let orderdate = o_h(lineitem.l_orderkey(i))(1)
            let orderyear = ext(`Year`, orderdate)
            let volume = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
            let brazil_volume = if(nationkey_to_name(s_h(lineitem.l_suppkey(i))(0))(0) == "BRAZIL") then volume else 0.0
            { orderyear -> < _ = brazil_volume, _ = volume > }

    sum(<k,v> <- l_h)
      { unique(< _ = k, _ = v(0) / v(1) >) -> true }
  ]
-/

end Tests.TPCH
