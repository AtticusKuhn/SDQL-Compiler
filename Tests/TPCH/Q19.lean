import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/19.sdql
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
-- let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
-- let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")
-- 
-- let p_h =
--   sum(<i,_> <- range(part.size))
--     if(
--         (
--           (part.p_brand(i) == "Brand#12")
--           && (
--                (part.p_container(i) == "SM CASE")
--                || (part.p_container(i) == "SM BOX")
--                || (part.p_container(i) == "SM PACK")
--                || (part.p_container(i) == "SM PKG")
--              )
--           && (1 <= part.p_size(i)) && (part.p_size(i) <= 5)
--         )
--         || (
--           (part.p_brand(i) == "Brand#23")
--           && (
--                (part.p_container(i) == "MED BAG")
--                || (part.p_container(i) == "MED BOX")
--                || (part.p_container(i) == "MED PACK")
--                || (part.p_container(i) == "MED PKG")
--              )
--           && (1 <= part.p_size(i)) && (part.p_size(i) <= 10)
--         )
--         || (
--           (part.p_brand(i) == "Brand#34")
--           && (
--                (part.p_container(i) == "LG CASE")
--                || (part.p_container(i) == "LG BOX")
--                || (part.p_container(i) == "LG PACK")
--                || (part.p_container(i) == "LG PKG")
--              )
--           && (1 <= part.p_size(i)) && (part.p_size(i) <= 15)
--         )
--     ) then
--       { unique(part.p_partkey(i)) ->
--         <
--           p_brand = part.p_brand(i),
--           p_size = part.p_size(i),
--           p_container = part.p_container(i)
--         >
--       }
-- 
-- let res =
--   sum(<i,_> <- range(lineitem.size))
--     let p_brand = p_h(lineitem.l_partkey(i))(0)
--     if(
--       (dom(p_h)(lineitem.l_partkey(i)))
--       && ((lineitem.l_shipmode(i) == "AIR") || (lineitem.l_shipmode(i) == "AIR REG"))
--       && (lineitem.l_shipinstruct(i) == "DELIVER IN PERSON")
--       && (
--            (
--              (p_brand == "Brand#12")
--              && (1.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 11.0)
--            )
--            || (
--              (p_brand == "Brand#23")
--              && (10.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 20.0)
--            )
--            || (
--              (p_brand == "Brand#34")
--              && (20.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 30.0)
--            )
--       )
--     ) then
--       lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))
-- 
-- { < revenue = res > -> true }
-- END SDQL

-- Stub SProg to keep module usable
unsafe def Q19_stub : SProg2 := [SDQLProg2 { int }| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def Q19 : SProg :=
  [SDQLProg { int }|
    let lineitem = load[<l_orderkey: @vec {int -> int}, l_partkey: @vec {int -> int}, l_suppkey: @vec {int -> int}, l_linenumber: @vec {int -> int}, l_quantity: @vec {int -> real}, l_extendedprice: @vec {int -> real}, l_discount: @vec {int -> real}, l_tax: @vec {int -> real}, l_returnflag: @vec {int -> varchar(1)}, l_linestatus: @vec {int -> varchar(1)}, l_shipdate: @vec {int -> date}, l_commitdate: @vec {int -> date}, l_receiptdate: @vec {int -> date}, l_shipinstruct: @vec {int -> varchar(25)}, l_shipmode: @vec {int -> varchar(10)}, l_comment: @vec {int -> varchar(44)}, size: int>]("datasets/tpch/lineitem.tbl")
    let part = load[<p_partkey: @vec {int -> int}, p_name: @vec {int -> varchar(55)}, p_mfgr: @vec {int -> varchar(25)}, p_brand: @vec {int -> varchar(10)}, p_type: @vec {int -> varchar(25)}, p_size: @vec {int -> int}, p_container: @vec {int -> varchar(10)}, p_retailprice: @vec {int -> real}, p_comment: @vec {int -> varchar(23)}, size: int>]("datasets/tpch/part.tbl")

    let p_h =
      sum(<i,_> <- range(part.size))
        if(
            (
              (part.p_brand(i) == "Brand#12")
              && (
                   (part.p_container(i) == "SM CASE")
                   || (part.p_container(i) == "SM BOX")
                   || (part.p_container(i) == "SM PACK")
                   || (part.p_container(i) == "SM PKG")
                 )
              && (1 <= part.p_size(i)) && (part.p_size(i) <= 5)
            )
            || (
              (part.p_brand(i) == "Brand#23")
              && (
                   (part.p_container(i) == "MED BAG")
                   || (part.p_container(i) == "MED BOX")
                   || (part.p_container(i) == "MED PACK")
                   || (part.p_container(i) == "MED PKG")
                 )
              && (1 <= part.p_size(i)) && (part.p_size(i) <= 10)
            )
            || (
              (part.p_brand(i) == "Brand#34")
              && (
                   (part.p_container(i) == "LG CASE")
                   || (part.p_container(i) == "LG BOX")
                   || (part.p_container(i) == "LG PACK")
                   || (part.p_container(i) == "LG PKG")
                 )
              && (1 <= part.p_size(i)) && (part.p_size(i) <= 15)
            )
        ) then
          { unique(part.p_partkey(i)) ->
            <
              p_brand = part.p_brand(i),
              p_size = part.p_size(i),
              p_container = part.p_container(i)
            >
          }

    let res =
      sum(<i,_> <- range(lineitem.size))
        let p_brand = p_h(lineitem.l_partkey(i))(0)
        if(
          (dom(p_h)(lineitem.l_partkey(i)))
          && ((lineitem.l_shipmode(i) == "AIR") || (lineitem.l_shipmode(i) == "AIR REG"))
          && (lineitem.l_shipinstruct(i) == "DELIVER IN PERSON")
          && (
               (
                 (p_brand == "Brand#12")
                 && (1.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 11.0)
               )
               || (
                 (p_brand == "Brand#23")
                 && (10.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 20.0)
               )
               || (
                 (p_brand == "Brand#34")
                 && (20.0 <= lineitem.l_quantity(i)) && (lineitem.l_quantity(i) <= 30.0)
               )
          )
        ) then
          lineitem.l_extendedprice(i) * (1.0 - lineitem.l_discount(i))

    { < revenue = res > -> true }
  ]
-/

end Tests.TPCH
