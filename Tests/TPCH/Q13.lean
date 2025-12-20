import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/13.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     let idx_special = ext(`FirstIndex`, orders.o_comment(i), "special")
--     if((idx_special == -1) || (ext(`LastIndex`, orders.o_comment(i), "requests") < (idx_special + 7))) then
--         { orders.o_custkey(i) -> 1 }
-- 
-- let c_h =
--   sum(<i,_> <- range(customer.size))
--     { < custkey = if(dom(o_h)(customer.c_custkey(i))) then o_h(customer.c_custkey(i)) else 0 > -> < count = 1 > }
-- 
-- sum(<k,v> <- c_h)
--   { unique(concat(k, v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q13_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q13 : SProg :=
  [SDQLProg { int }|
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")

    let o_h =
      sum(<i,_> <- range(orders.size))
        let idx_special = ext(`FirstIndex`, orders.o_comment(i), "special")
        if((idx_special == -1) || (ext(`LastIndex`, orders.o_comment(i), "requests") < (idx_special + 7))) then
            { orders.o_custkey(i) -> 1 }

    let c_h =
      sum(<i,_> <- range(customer.size))
        { < custkey = if(dom(o_h)(customer.c_custkey(i))) then o_h(customer.c_custkey(i)) else 0 > -> < count = 1 > }

    sum(<k,v> <- c_h)
      { unique(concat(k, v)) -> true }
  ]
-/

end Tests.TPCH
