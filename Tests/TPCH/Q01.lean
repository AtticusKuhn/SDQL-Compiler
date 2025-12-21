import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/1.sdql

This is a (nearly) direct port of the full Q01 query.

Note: our surface record types are canonicalized by sorting fields, so for TPCH
output compatibility we use positional-style field names `_1.._7`.
-/

unsafe def Q01 : SProg2 :=
  [SDQLProg2 { { < _1 : string, _2 : string, _3 : real, _4 : real, _5 : real, _6 : real, _7 : int > -> bool } }|
    let lineitem = load[<
      l_orderkey: @vec {int -> int},
      l_partkey: @vec {int -> int},
      l_suppkey: @vec {int -> int},
      l_linenumber: @vec {int -> int},
      l_quantity: @vec {int -> real},
      l_extendedprice: @vec {int -> real},
      l_discount: @vec {int -> real},
      l_tax: @vec {int -> real},
      l_returnflag: @vec {int -> varchar(1)},
      l_linestatus: @vec {int -> varchar(1)},
      l_shipdate: @vec {int -> date},
      l_commitdate: @vec {int -> date},
      l_receiptdate: @vec {int -> date},
      l_shipinstruct: @vec {int -> varchar(25)},
      l_shipmode: @vec {int -> varchar(10)},
      l_comment: @vec {int -> varchar(44)},
      size: int
    >]("datasets/tpch-tiny/lineitem.tbl") in

    let l_h =
      sum(<i,_v> in range(lineitem.size))
        if (lineitem.l_shipdate(i) <= date (19980902)) then
          { < _1 = lineitem.l_returnflag(i), _2 = lineitem.l_linestatus(i) > ->
             <
               _3 = lineitem.l_quantity(i),
               _4 = lineitem.l_extendedprice(i),
               _5 = lineitem.l_extendedprice(i) *{real} (1.0 - lineitem.l_discount(i)),
               _6 = (lineitem.l_extendedprice(i) *{real} (1.0 - lineitem.l_discount(i))) *{real} (1.0 + lineitem.l_tax(i)),
               _7 = 1
             >
          }
        else {}_{ < _1 : string, _2 : string >,
                  < _3 : real, _4 : real, _5 : real, _6 : real, _7 : int > } in

    sum(<k,v> in l_h)
      { unique(concat(k,v)) -> true }
  ]

#print Q01

end Tests.TPCH
