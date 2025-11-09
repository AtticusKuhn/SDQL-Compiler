import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/16.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if(
--       (part.p_brand(i) != "Brand#45") &&
--       !ext(`StrStartsWith`, part.p_type(i), "MEDIUM POLISHED") &&
--       (
--         (part.p_size(i) ==  49) ||
--         (part.p_size(i) ==  14) ||
--         (part.p_size(i) ==  23) ||
--         (part.p_size(i) ==  45) ||
--         (part.p_size(i) ==  19) ||
--         (part.p_size(i) ==  3) ||
--         (part.p_size(i) ==  36) ||
--         (part.p_size(i) ==  9)
--       )
--     ) then
--       { unique(part.p_partkey(i)) -> < _ = part.p_brand(i), _ = part.p_type(i), _ = part.p_size(i) > }
-- 
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     let idx_customer = ext(`FirstIndex`, supplier.s_comment(i), "Customer")
--     if((idx_customer != -1) && (idx_customer + 8 <= ext(`FirstIndex`, supplier.s_comment(i), "Complaints"))) then
--       { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_suppkey(i) > }
-- 
-- let ps_h =
--   sum(<i,_> <- range(partsupp.size))
--     if ((dom(p_h)(partsupp.ps_partkey(i))) && (!(dom(s_h)(partsupp.ps_suppkey(i))))) then
--     {
--       <
--         brand = p_h(partsupp.ps_partkey(i))(0),
--         type = p_h(partsupp.ps_partkey(i))(1),
--         size = p_h(partsupp.ps_partkey(i))(2)
--       > ->
--       { partsupp.ps_suppkey(i) -> 1 }
--     }
-- 
-- // FIXME rename v_hashmap to v
-- sum(<k,v_hashmap> <- ps_h)
--   { unique(concat(k, < _ = ext(`Size`, v_hashmap) >)) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q16_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q16 : SProg :=
  [SDQLProg { int }|
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")

    let p_h =
      sum(<i,_> <- range(part.size))
        if(
          (part.p_brand(i) != "Brand#45") &&
          !ext(`StrStartsWith`, part.p_type(i), "MEDIUM POLISHED") &&
          (
            (part.p_size(i) ==  49) ||
            (part.p_size(i) ==  14) ||
            (part.p_size(i) ==  23) ||
            (part.p_size(i) ==  45) ||
            (part.p_size(i) ==  19) ||
            (part.p_size(i) ==  3) ||
            (part.p_size(i) ==  36) ||
            (part.p_size(i) ==  9)
          )
        ) then
          { unique(part.p_partkey(i)) -> < _ = part.p_brand(i), _ = part.p_type(i), _ = part.p_size(i) > }

    let s_h =
      sum(<i,_> <- range(supplier.size))
        let idx_customer = ext(`FirstIndex`, supplier.s_comment(i), "Customer")
        if((idx_customer != -1) && (idx_customer + 8 <= ext(`FirstIndex`, supplier.s_comment(i), "Complaints"))) then
          { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_suppkey(i) > }

    let ps_h =
      sum(<i,_> <- range(partsupp.size))
        if ((dom(p_h)(partsupp.ps_partkey(i))) && (!(dom(s_h)(partsupp.ps_suppkey(i))))) then
        {
          <
            brand = p_h(partsupp.ps_partkey(i))(0),
            type = p_h(partsupp.ps_partkey(i))(1),
            size = p_h(partsupp.ps_partkey(i))(2)
          > ->
          { partsupp.ps_suppkey(i) -> 1 }
        }

    // FIXME rename v_hashmap to v
    sum(<k,v_hashmap> <- ps_h)
      { unique(concat(k, < _ = ext(`Size`, v_hashmap) >)) -> true }
  ]
-/

end Tests.TPCH
