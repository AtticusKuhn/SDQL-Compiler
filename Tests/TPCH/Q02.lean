import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/2.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl")
-- 
-- let l_h =
--   sum(<i,_> <- range(region.size))
--     if(region.r_name(i) == "EUROPE") then
--       { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > }
-- 
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     if(dom(l_h)(nation.n_regionkey(i))) then
--       { unique(nation.n_nationkey(i)) -> nation.n_name(i) }
-- 
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     if(dom(n_h)(supplier.s_nationkey(i))) then
--       {
--         unique(supplier.s_suppkey(i)) ->
--         <
--           _ = supplier.s_acctbal(i),
--           _ = supplier.s_name(i),
--           _ = n_h(supplier.s_nationkey(i)),
--           _ = supplier.s_address(i),
--           _ = supplier.s_phone(i),
--           _ = supplier.s_comment(i)
--         >
--       }
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if((part.p_size(i) == 15) && (ext(`StrEndsWith`, part.p_type(i), "BRASS"))) then
--       { unique(part.p_partkey(i)) -> < _ = part.p_mfgr(i) > }
-- 
-- let ps_h =
--   sum(<i,_> <- range(partsupp.size))
--     if ((dom(p_h)(partsupp.ps_partkey(i))) && (dom(s_h)(partsupp.ps_suppkey(i)))) then
--       { partsupp.ps_partkey(i) -> partsupp.ps_supplycost(i) }
-- 
-- sum(<i,_> <- range(partsupp.size))
--   if(
--       (dom(ps_h)(partsupp.ps_partkey(i)))
--       && (ps_h(partsupp.ps_partkey(i)) == partsupp.ps_supplycost(i))
--       && (dom(s_h)(partsupp.ps_suppkey(i)))
--     ) then
--     {
--       unique(<
--         _ = s_h(partsupp.ps_suppkey(i))(0),
--         _ = s_h(partsupp.ps_suppkey(i))(1),
--         _ = s_h(partsupp.ps_suppkey(i))(2),
--         _ = partsupp.ps_partkey(i),
--         _ = p_h(partsupp.ps_partkey(i))(0),
--         _ = s_h(partsupp.ps_suppkey(i))(4),
--         _ = s_h(partsupp.ps_suppkey(i))(3),
--         _ = s_h(partsupp.ps_suppkey(i))(5)
--       >) -> true
--     }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q02_stub : SProg := [SDQLProg { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q02 : SProg :=
  [SDQLProg { int }|
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
    let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/region.tbl")

    let l_h =
      sum(<i,_> <- range(region.size))
        if(region.r_name(i) == "EUROPE") then
          { unique(region.r_regionkey(i)) -> < _ = region.r_regionkey(i) > }

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(dom(l_h)(nation.n_regionkey(i))) then
          { unique(nation.n_nationkey(i)) -> nation.n_name(i) }

    let s_h =
      sum(<i,_> <- range(supplier.size))
        if(dom(n_h)(supplier.s_nationkey(i))) then
          {
            unique(supplier.s_suppkey(i)) ->
            <
              _ = supplier.s_acctbal(i),
              _ = supplier.s_name(i),
              _ = n_h(supplier.s_nationkey(i)),
              _ = supplier.s_address(i),
              _ = supplier.s_phone(i),
              _ = supplier.s_comment(i)
            >
          }

    let p_h =
      sum(<i,_> <- range(part.size))
        if((part.p_size(i) == 15) && (ext(`StrEndsWith`, part.p_type(i), "BRASS"))) then
          { unique(part.p_partkey(i)) -> < _ = part.p_mfgr(i) > }

    let ps_h =
      sum(<i,_> <- range(partsupp.size))
        if ((dom(p_h)(partsupp.ps_partkey(i))) && (dom(s_h)(partsupp.ps_suppkey(i)))) then
          { partsupp.ps_partkey(i) -> partsupp.ps_supplycost(i) }

    sum(<i,_> <- range(partsupp.size))
      if(
          (dom(ps_h)(partsupp.ps_partkey(i)))
          && (ps_h(partsupp.ps_partkey(i)) == partsupp.ps_supplycost(i))
          && (dom(s_h)(partsupp.ps_suppkey(i)))
        ) then
        {
          unique(<
            _ = s_h(partsupp.ps_suppkey(i))(0),
            _ = s_h(partsupp.ps_suppkey(i))(1),
            _ = s_h(partsupp.ps_suppkey(i))(2),
            _ = partsupp.ps_partkey(i),
            _ = p_h(partsupp.ps_partkey(i))(0),
            _ = s_h(partsupp.ps_suppkey(i))(4),
            _ = s_h(partsupp.ps_suppkey(i))(3),
            _ = s_h(partsupp.ps_suppkey(i))(5)
          >) -> true
        }
  ]
-/

end Tests.TPCH
