import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/11.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl")
-- let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl")
-- let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl")
--
-- let n_h =
--   sum(<i,_> <- range(nation.size))
--     if(nation.n_name(i) == "GERMANY") then
--       { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > }
--
-- let s_h =
--   sum(<i,_> <- range(supplier.size))
--     if(dom(n_h)(supplier.s_nationkey(i))) then
--       { unique(supplier.s_suppkey(i)) -> true }
--
-- let ps_t =
--   sum(<i,_> <- range(partsupp.size))
--     if(dom(s_h)(partsupp.ps_suppkey(i))) then
--       <
--         _ = partsupp.ps_supplycost(i) * partsupp.ps_availqty(i) * 0.0001,
--         _ = { partsupp.ps_partkey(i) -> partsupp.ps_supplycost(i) * partsupp.ps_availqty(i) }
--       >
--
-- let <ps_t_0, ps_t_1> = ps_t
--
-- sum(<ps_partkey,ps_supplycost> <-  ps_t_1)
--   if(ps_t_0 < ps_supplycost) then
--     { unique(< _ = ps_partkey, _ = ps_supplycost >) -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q11_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)

unsafe def Q11 : SProg2 :=
  [SDQLProg2 { { < _ : int, _ : real > -> bool } }|
    let supplier = load[<s_suppkey: @vec {int -> int}, s_name: @vec {int -> varchar(25)}, s_address: @vec {int -> varchar(40)}, s_nationkey: @vec {int -> int}, s_phone: @vec {int -> varchar(15)}, s_acctbal: @vec {int -> real}, s_comment: @vec {int -> varchar(101)}, size: int>]("datasets/tpch/supplier.tbl") in
    let partsupp = load[<ps_partkey: @vec {int -> int}, ps_suppkey: @vec {int -> int}, ps_availqty: @vec {int -> real}, ps_supplycost: @vec {int -> real}, ps_comment: @vec {int -> varchar(199)}, size: int>]("datasets/tpch/partsupp.tbl") in
    let nation = load[<n_nationkey: @vec {int -> int}, n_name: @vec {int -> varchar(25)}, n_regionkey: @vec {int -> int}, n_comment: @vec {int -> varchar(152)}, size: int>]("datasets/tpch/nation.tbl") in

    let n_h =
      sum(<i,_> <- range(nation.size))
        if(nation.n_name(i) == "GERMANY") then
          { unique(nation.n_nationkey(i)) -> < _ = nation.n_nationkey(i) > } in

    let s_h =
      sum(<i,_> <- range(supplier.size))
        if(dom(n_h)(supplier.s_nationkey(i))) then
          { unique(supplier.s_suppkey(i)) -> true } in

    let ps_t =
      sum(<i,_> <- range(partsupp.size))
        if(dom(s_h)(partsupp.ps_suppkey(i))) then
          <
            _ = partsupp.ps_supplycost(i) * partsupp.ps_availqty(i) * 0.0001,
            _ = { partsupp.ps_partkey(i) -> partsupp.ps_supplycost(i) * partsupp.ps_availqty(i) }
          > in

    -- let <ps_t_0, ps_t_1> = ps_t in

    sum(<ps_partkey,ps_supplycost> <-  ps_t(1) )
      if(ps_t(0) < ps_supplycost) then
        { unique(< _ = ps_partkey, _ = ps_supplycost >) -> true }
  ]


end Tests.TPCH
