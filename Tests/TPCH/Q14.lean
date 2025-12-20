import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/14.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if(ext(`StrStartsWith`, part.p_type(i), "PROMO")) then
--       { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }
-- 
-- let l_t =
--   sum(<i,_> <- range(lineitem.size))
--     if((date(19950901) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19951001))) then
--       <
--         a = if (dom(p_h)(lineitem.l_partkey(i))) then lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) else 0.0,
--         b = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)),
--       >
-- 
-- 100.0 * l_t.a / l_t.b
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q14_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q14 : SProg :=
  [SDQLProg { int }|
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")

    let p_h =
      sum(<i,_> <- range(part.size))
        if(ext(`StrStartsWith`, part.p_type(i), "PROMO")) then
          { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }

    let l_t =
      sum(<i,_> <- range(lineitem.size))
        if((date(19950901) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19951001))) then
          <
            a = if (dom(p_h)(lineitem.l_partkey(i))) then lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)) else 0.0,
            b = lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i)),
          >

    100.0 * l_t.a / l_t.b
  ]
-/

end Tests.TPCH
