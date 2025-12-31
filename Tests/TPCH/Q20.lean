import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/20.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if(ext(`StrStartsWith`, part.p_name(i), "forest")) then
--       { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }
-- 
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     if(nation.n_name(i) == "CANADA") then
--       { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > }
-- 
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     if(dom(n_h)(supplier.s_nationkey(i))) then
--       { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_suppkey(i) > }
-- 
-- let l_h =
--   sum(<i,_> <- range(lineitem.size))
--     if(
--       (date(19940101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19950101))
--       && (dom(p_h)(lineitem.l_partkey(i))) && (dom(s_h)(lineitem.l_suppkey(i)))
--       ) then
--       { unique(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >) -> 0.5 * lineitem.l_quantity(i) }
-- 
-- let ps_h =
--   sum(<i,_> <- range(partsupp.size))
--     let key = <_ = partsupp.ps_partkey(i), _ = partsupp.ps_suppkey(i) >
--     if((dom(l_h)(key)) && (l_h(key) < partsupp.ps_availqty(i))) then
--       { unique(partsupp.ps_suppkey(i)) -> < _ = partsupp.ps_suppkey(i) > }
-- 
-- sum(<i,_> <- range(supplier.size))
--   if(dom(ps_h)(supplier.s_suppkey(i))) then
--     { unique(< _ = supplier.s_name(i), _ = supplier.s_address(i) >) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q20_stub : SProg2 := [SDQLProg2 { int }| 0 ]

unsafe def Q20 : SProg2 :=
  [SDQLProg2 { { < _1 : varchar(25), _2 : varchar(40) > -> bool } }|
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl") in
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl") in
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl") in
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl") in
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl") in

    let p_h =
      sum(<i,_> <- range(part.size))
        if(StrStartsWith(part.p_name(i), "forest")) then
          { unique(part.p_partkey(i)) -> true } in

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(nation.n_name(i) == "CANADA") then
          { unique(nation.n_nationkey(i)) -> true } in

    let s_h =
      sum(<i,_> <- range(supplier.size))
        if(dom(n_h)(supplier.s_nationkey(i))) then
          { unique(supplier.s_suppkey(i)) -> true } in

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
          (date(19940101) <= lineitem.l_shipdate(i)) &&
          (lineitem.l_shipdate(i) < date(19950101)) &&
          (dom(p_h)(lineitem.l_partkey(i))) &&
          (dom(s_h)(lineitem.l_suppkey(i)))
        ) then
          { unique(< _1 = lineitem.l_partkey(i), _2 = lineitem.l_suppkey(i) >) -> 0.5 * lineitem.l_quantity(i) } in

    let ps_h =
      sum(<i,_> <- range(partsupp.size))
        let key = < _1 = partsupp.ps_partkey(i), _2 = partsupp.ps_suppkey(i) > in
        if((dom(l_h)(key)) && (l_h(key) < partsupp.ps_availqty(i))) then
          { unique(partsupp.ps_suppkey(i)) -> true } in

    sum(<i,_> <- range(supplier.size))
      if(dom(ps_h)(supplier.s_suppkey(i))) then
        { unique(< _1 = supplier.s_name(i), _2 = supplier.s_address(i) >) -> true }
  ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q20 : SProg :=
  [SDQLProg { int }|
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")

    let p_h =
      sum(<i,_> <- range(part.size))
        if(ext(`StrStartsWith`, part.p_name(i), "forest")) then
          { unique(part.p_partkey(i)) -> < _ = part.p_partkey(i) > }

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(nation.n_name(i) == "CANADA") then
          { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > }

    let s_h =
      sum(<i,_> <- range(supplier.size))
        if(dom(n_h)(supplier.s_nationkey(i))) then
          { unique(supplier.s_suppkey(i)) -> < _ = supplier.s_suppkey(i) > }

    let l_h =
      sum(<i,_> <- range(lineitem.size))
        if(
          (date(19940101) <= lineitem.l_shipdate(i)) && (lineitem.l_shipdate(i) < date(19950101))
          && (dom(p_h)(lineitem.l_partkey(i))) && (dom(s_h)(lineitem.l_suppkey(i)))
          ) then
          { unique(< _ = lineitem.l_partkey(i), _ = lineitem.l_suppkey(i) >) -> 0.5 * lineitem.l_quantity(i) }

    let ps_h =
      sum(<i,_> <- range(partsupp.size))
        let key = <_ = partsupp.ps_partkey(i), _ = partsupp.ps_suppkey(i) >
        if((dom(l_h)(key)) && (l_h(key) < partsupp.ps_availqty(i))) then
          { unique(partsupp.ps_suppkey(i)) -> < _ = partsupp.ps_suppkey(i) > }

    sum(<i,_> <- range(supplier.size))
      if(dom(ps_h)(supplier.s_suppkey(i))) then
        { unique(< _ = supplier.s_name(i), _ = supplier.s_address(i) >) -> true }
  ]
-/

end Tests.TPCH
