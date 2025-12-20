import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/21.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- 
-- let nation_indexed =
--   sum(<i,_> <- range(nation.size))
--     if(nation.n_name(i) == "SAUDI ARABIA") then
--       { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > }
-- 
-- let su_probed =
--   sum(<i,_> <- range(supplier.size))
--     if(dom(nation_indexed)(supplier.s_nationkey(i))) then
--       { unique(supplier.s_suppkey(i)) -> supplier.s_name(i) }
-- 
-- let ord_indexed =
--   sum(<i,_> <- range(orders.size))
--     if(orders.o_orderstatus(i) == "F") then
--       @vec(6000001) { orders.o_orderkey(i) -> true }
-- 
-- let l2_indexed =
--   sum(<i,_> <- range(lineitem.size))
--     @vec(6000001) { lineitem.l_orderkey(i) -> @smallvecdict(4) { lineitem.l_suppkey(i) -> 1 } }
-- 
-- let l3_indexed =
--   sum(<i,_> <- range(lineitem.size))
--     if(lineitem.l_commitdate(i) < lineitem.l_receiptdate(i)) then
--       @vec(6000001) { lineitem.l_orderkey(i) -> @smallvecdict(4) { lineitem.l_suppkey(i) -> 1 } }
-- 
-- let l1_probed =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--       (lineitem.l_commitdate(i) < lineitem.l_receiptdate(i)) &&
--       (dom(su_probed)(lineitem.l_suppkey(i))) &&
--       (dom(ord_indexed)(lineitem.l_orderkey(i))) &&
--       (1 < ext(`Size`, l2_indexed(lineitem.l_orderkey(i)))) &&
--       (ext(`Size`, l3_indexed(lineitem.l_orderkey(i))) <= 1)
--     ) then
--       { < name = su_probed(lineitem.l_suppkey(i)) > -> < numwait = 1> }
-- 
-- sum(<k,v> <- l1_probed)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q21_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q21 : SProg :=
  [SDQLProg { int }|
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")

    let nation_indexed =
      sum(<i,_> <- range(nation.size))
        if(nation.n_name(i) == "SAUDI ARABIA") then
          { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > }

    let su_probed =
      sum(<i,_> <- range(supplier.size))
        if(dom(nation_indexed)(supplier.s_nationkey(i))) then
          { unique(supplier.s_suppkey(i)) -> supplier.s_name(i) }

    let ord_indexed =
      sum(<i,_> <- range(orders.size))
        if(orders.o_orderstatus(i) == "F") then
          @vec(6000001) { orders.o_orderkey(i) -> true }

    let l2_indexed =
      sum(<i,_> <- range(lineitem.size))
        @vec(6000001) { lineitem.l_orderkey(i) -> @smallvecdict(4) { lineitem.l_suppkey(i) -> 1 } }

    let l3_indexed =
      sum(<i,_> <- range(lineitem.size))
        if(lineitem.l_commitdate(i) < lineitem.l_receiptdate(i)) then
          @vec(6000001) { lineitem.l_orderkey(i) -> @smallvecdict(4) { lineitem.l_suppkey(i) -> 1 } }

    let l1_probed =
      sum(<i,_> <- range(lineitem.size))
        if(
          (lineitem.l_commitdate(i) < lineitem.l_receiptdate(i)) &&
          (dom(su_probed)(lineitem.l_suppkey(i))) &&
          (dom(ord_indexed)(lineitem.l_orderkey(i))) &&
          (1 < ext(`Size`, l2_indexed(lineitem.l_orderkey(i)))) &&
          (ext(`Size`, l3_indexed(lineitem.l_orderkey(i))) <= 1)
        ) then
          { < name = su_probed(lineitem.l_suppkey(i)) > -> < numwait = 1> }

    sum(<k,v> <- l1_probed)
      { unique(concat(k,v)) -> true }
  ]
-/

end Tests.TPCH
