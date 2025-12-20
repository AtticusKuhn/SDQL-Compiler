import PartIiProject.SyntaxSDQLProg

namespace Tests.TPCH

open PartIiProject

/-
Source: sdql-rs/progs/tpch/1.sdql

This is a simplified version that tests the basic Q01 computation:
group by (returnflag, linestatus) and sum quantities.
We skip the complex agg1/agg2 computations for now.
-/

-- Simplified Q01: just sum l_quantity grouped by (returnflag, linestatus)
-- Key: <linestatus: string, returnflag: string> (sorted alphabetically)
-- Value: <l_quantity_sum: real, mult: int>

unsafe def Q01 : SProg2 :=
  [SDQLProg2 { { < linestatus : string, returnflag : string > ->
               < l_quantity_sum : real, mult : int > } }|
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

    let cutoff = date ( 19980902 ) in
    sum(<i,_v> in range(lineitem.size))
      if((lineitem.l_shipdate(i)) <= cutoff) then
        { < returnflag = lineitem.l_returnflag(i), linestatus = lineitem.l_linestatus(i) > ->
           <
             l_quantity_sum = lineitem.l_quantity(i),
             mult = 1
           >
        }
      else {}_{ < linestatus : string, returnflag : string >,
                < l_quantity_sum : real, mult : int > }
  ]

#print Q01

end Tests.TPCH
