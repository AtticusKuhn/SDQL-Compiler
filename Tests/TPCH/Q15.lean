import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/15.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- 
-- let suppkey_to_revenue =
--   sum(<i,_> <- range(lineitem.size))
--     if((date(19960101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19960401))) then
--       { lineitem.l_suppkey(i) -> lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) }
-- 
-- let max_revenue = sum(<_,v> <- suppkey_to_revenue) promote[max_prod](v)
-- 
-- let suppkey_to_supp =
--   sum(<i,_> <- range(supplier.size))
--     {
--       unique(supplier.s_suppkey(i)) ->
--       <
--         name = supplier.s_name(i),
--         address = supplier.s_address(i),
--         phone = supplier.s_phone(i)
--       >
--     }
-- 
-- sum(<suppkey,revenue> <- suppkey_to_revenue)
--   if(revenue == max_revenue) then
--     {
--       unique(
--         <
--           suppkey = suppkey,
--           // FIXME redundant brackets
--           name = (suppkey_to_supp(suppkey)).name,
--           address = (suppkey_to_supp(suppkey)).address,
--           phone = (suppkey_to_supp(suppkey)).phone,
--           total_revenue = revenue
--         >
--       ) -> true
--     }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q15_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q15 : SProg :=
  [SDQLProg { int }|
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")

    let suppkey_to_revenue =
      sum(<i,_> <- range(lineitem.size))
        if((date(19960101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19960401))) then
          { lineitem.l_suppkey(i) -> lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) }

    let max_revenue = sum(<_,v> <- suppkey_to_revenue) promote[max_prod](v)

    let suppkey_to_supp =
      sum(<i,_> <- range(supplier.size))
        {
          unique(supplier.s_suppkey(i)) ->
          <
            name = supplier.s_name(i),
            address = supplier.s_address(i),
            phone = supplier.s_phone(i)
          >
        }

    sum(<suppkey,revenue> <- suppkey_to_revenue)
      if(revenue == max_revenue) then
        {
          unique(
            <
              suppkey = suppkey,
              // FIXME redundant brackets
              name = (suppkey_to_supp(suppkey)).name,
              address = (suppkey_to_supp(suppkey)).address,
              phone = (suppkey_to_supp(suppkey)).phone,
              total_revenue = revenue
            >
          ) -> true
        }
  ]
-/

end Tests.TPCH
