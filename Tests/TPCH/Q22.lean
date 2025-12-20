import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/22.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
-- let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")
-- 
-- let o_h =
--   sum(<i,_> <- range(orders.size))
--     @vec(150001) { orders.o_custkey(i) -> true }
-- 
-- let fused =
--   sum(<i,_> <- range(customer.size))
--     let cond = (
--                  (0.0 < customer.c_acctbal(i)) &&
--                  (
--                    // FIXME remove unnecessary parentheses
--                    (ext(`StrStartsWith`, customer.c_phone(i), "13")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "31")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "23")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "29")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "30")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "18")) ||
--                    (ext(`StrStartsWith`, customer.c_phone(i), "17"))
--                  )
--                ) in
--     < total = if(cond) then customer.c_acctbal(i) else 0.0, count = if(cond) then 1.0 else 0.0 >
-- 
-- let avg = fused.total / fused.count
-- 
-- let res =
--   sum(<i,_> <- range(customer.size))
--     if(
--       (avg < customer.c_acctbal(i)) &&
--       (o_h(customer.c_custkey(i)) == false) &&
--       (
--         // FIXME remove unnecessary parentheses
--         (ext(`StrStartsWith`, customer.c_phone(i), "13")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "31")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "23")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "29")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "30")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "18")) ||
--         (ext(`StrStartsWith`, customer.c_phone(i), "17"))
--       )
--     ) then
--       { < cntrycode = ext(`SubString`, customer.c_phone(i), 0, 2) > -> < numcust = 1, totacctbal = customer.c_acctbal(i) > }
-- 
-- sum(<k,v> <- res)
--   { unique(concat(k,v)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q22_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q22 : SProg :=
  [SDQLProg { int }|
    let customer = load[<c_custkey: @vec {int -> int}, c_name: @vec {int -> varchar(25)}, c_address: @vec {int -> varchar(40)}, c_nationkey: @vec {int -> int}, c_phone: @vec {int -> varchar(15)}, c_acctbal: @vec {int -> real}, c_mktsegment: @vec {int -> varchar(10)}, c_comment: @vec {int -> varchar(117)}, size: int>]("datasets/tpch/customer.tbl")
    let orders = load[<o_orderkey: @vec {int -> int}, o_custkey: @vec {int -> int}, o_orderstatus: @vec {int -> varchar(1)}, o_totalprice: @vec {int -> real}, o_orderdate: @vec {int -> date}, o_orderpriority: @vec {int -> varchar(15)}, o_clerk: @vec {int -> varchar(15)}, o_shippriority: @vec {int -> int}, o_comment: @vec {int -> varchar(79)}, size: int>]("datasets/tpch/orders.tbl")

    let o_h =
      sum(<i,_> <- range(orders.size))
        @vec(150001) { orders.o_custkey(i) -> true }

    let fused =
      sum(<i,_> <- range(customer.size))
        let cond = (
                     (0.0 < customer.c_acctbal(i)) &&
                     (
                       // FIXME remove unnecessary parentheses
                       (ext(`StrStartsWith`, customer.c_phone(i), "13")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "31")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "23")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "29")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "30")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "18")) ||
                       (ext(`StrStartsWith`, customer.c_phone(i), "17"))
                     )
                   ) in
        < total = if(cond) then customer.c_acctbal(i) else 0.0, count = if(cond) then 1.0 else 0.0 >

    let avg = fused.total / fused.count

    let res =
      sum(<i,_> <- range(customer.size))
        if(
          (avg < customer.c_acctbal(i)) &&
          (o_h(customer.c_custkey(i)) == false) &&
          (
            // FIXME remove unnecessary parentheses
            (ext(`StrStartsWith`, customer.c_phone(i), "13")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "31")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "23")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "29")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "30")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "18")) ||
            (ext(`StrStartsWith`, customer.c_phone(i), "17"))
          )
        ) then
          { < cntrycode = ext(`SubString`, customer.c_phone(i), 0, 2) > -> < numcust = 1, totacctbal = customer.c_acctbal(i) > }

    sum(<k,v> <- res)
      { unique(concat(k,v)) -> true }
  ]
-/

end Tests.TPCH
