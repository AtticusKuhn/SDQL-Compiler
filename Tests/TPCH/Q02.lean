import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore
import PartIiProject.CodegenRust
import PartIiProject.Term2

namespace Tests.TPCH
open PartIiProject.SurfaceTy

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

-- Stub SProg2 to keep module usable (DeBruijn pipeline)
unsafe def Q02_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
  Simplified Q02: demonstrate loads, range, dom, &&, ==, and endsWith.
  This is not semantically faithful; it exists to exercise the syntax and typing.
  The attempt below is kept for reference but is no longer elaborated directly; see
  `Tests/TPCH/Q02RecordNameMismatch.lean` for a minimized reproducer of the record-label issue.
-/

unsafe def Q02_wip : SProg2 :=
  -- Result type: (acctbal, name, nation_name, partkey, mfgr, phone, address, comment)
  -- Fields sorted by name: _1 < _2 < _3 < _4 < _5 < _6 < _7 < _8
  [SDQLProg2 { { < _1 : real, _2 : string, _3 : string, _4 : int, _5 : string, _6 : string, _7 : string, _8 : string > -> bool } }|
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch-tiny/part.tbl") in
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch-tiny/supplier.tbl") in
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch-tiny/partsupp.tbl") in
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch-tiny/nation.tbl") in
    let region = load[<r_regionkey: @vec {int -> int}, r_name: @vec {int -> varchar(25)}, r_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch-tiny/region.tbl") in

    let l_h =
      sum(<i,_v> <- range(region.size))
        if(region.r_name(i) == "EUROPE") then
          { unique(region.r_regionkey(i)) -> < _v = region.r_regionkey(i) > }
        else {}_{ int, < _v : int > } in

    let n_h =
      sum(<i,_v> <- range(nation.size))
        if(dom(l_h)(nation.n_regionkey(i))) then
          { unique(nation.n_nationkey(i)) -> nation.n_name(i) }
        else {}_{ int, string } in

    -- s_h: suppkey -> (acctbal, name, nation_name, address, phone, comment)
    -- Fields: _1=acctbal, _2=name, _3=nation_name, _4=address, _5=phone, _6=comment
    let s_h =
      sum(<i,_v> <- range(supplier.size))
        if(dom(n_h)(supplier.s_nationkey(i))) then
          {
            unique(supplier.s_suppkey(i)) ->
            <
              _1 = supplier.s_acctbal(i),
              _2 = supplier.s_name(i),
              _3 = n_h(supplier.s_nationkey(i)),
              _4 = supplier.s_address(i),
              _5 = supplier.s_phone(i),
              _6 = supplier.s_comment(i)
            >
          }
        else {}_{ int, < _1 : real, _2 : string, _3 : string, _4 : string, _5 : string, _6 : string > } in

    let p_h =
      sum(<i,_v> <- range(part.size))
        if((part.p_size(i) == 15) && (endsWith(part.p_type(i), "BRASS"))) then
          { unique(part.p_partkey(i)) -> < _v = part.p_mfgr(i) > }
        else {}_{ int, < _v : string > } in

    let ps_h =
      sum(<i,_v> <- range(partsupp.size))
        if ((dom(p_h)(partsupp.ps_partkey(i))) && (dom(s_h)(partsupp.ps_suppkey(i)))) then
          { partsupp.ps_partkey(i) -> partsupp.ps_supplycost(i) }
        else {}_{ int, real } in

    -- Final result: (acctbal, name, nation_name, partkey, mfgr, phone, address, comment)
    sum(<i,_v> <- range(partsupp.size))
      if(
          (dom(ps_h)(partsupp.ps_partkey(i)))
          && (ps_h(partsupp.ps_partkey(i)) == partsupp.ps_supplycost(i))
          && (dom(s_h)(partsupp.ps_suppkey(i)))
        ) then
        {
          unique(<
            _1 = s_h(partsupp.ps_suppkey(i))._1,
            _2 = s_h(partsupp.ps_suppkey(i))._2,
            _3 = s_h(partsupp.ps_suppkey(i))._3,
            _4 = partsupp.ps_partkey(i),
            _5 = p_h(partsupp.ps_partkey(i))._v,
            _6 = s_h(partsupp.ps_suppkey(i))._5,
            _7 = s_h(partsupp.ps_suppkey(i))._4,
            _8 = s_h(partsupp.ps_suppkey(i))._6
          >) -> true
        }
      else {}_{ < _1 : real, _2 : string, _3 : string, _4 : int, _5 : string, _6 : string, _7 : string, _8 : string >, bool }
  ]

unsafe def Q02 : SProg2 := Q02_wip
#print Q02_wip
-- Generate Rust code from the DeBruijn pipeline
open ToCore2 in
#eval! IO.println (renderRustProg2Shown (trProg2 Q02_stub))

-- Generate Rust code for the full Q02 query
open ToCore2 in
#eval! IO.println (renderRustProg2Shown (trProg2 Q02))

#print Q02

end Tests.TPCH
