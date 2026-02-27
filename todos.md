- The implementation of `concat` in Rust is ugly, need to fix it.
- `sub` currently type `t -> t -> t`, should introduce a typeclass for it.
- Get github workflow to run successfully.
- Make `<` and `<=` and `==` use a typeclass (instead of taking in any type `t`)
- We currently use a bad representation of dates (i.e. YYYYMMDD as an `i64`). This is dumb.
- Q15 is tiny-only (SF=0.01 currently diverges due to missing
    promote[max_prod]/max-semirings).
- get rid of ugly `A *{Type} B` syntax
- Get rid of ugly `<_1 =..., _2 = ...>` syntax. Just replace this with `<..., ....>`
- the tuple_add4, tuple_add5 thing is annoying. Just replace with a macro.
- three of the supposed “optimisations” actually make the code slower. Horizontal_loop_fusion and loop_factorization_left and loop_invariant_code motion. I should investigate this, but I haven’t investigated this yet.
- Add `docs/pipeline.md` file documenting the current pipeline
- Add tree diagram with comments explaining each file.
- start writing paper (in typst or latex), and add to CI/CD
- optimisation pipeline is ugly, could this be improved by the use of a monad?
- Current rust implementation is slowed down a lot by overused of `x.clone()` in BTreeMap. I'm not good enough with Rust to avoid this.
- Use Rust profiling. Use a profiler for any serious performance analysis.
- Need to make semi-ring multiplication actually work
- need to implement `closure(e)`
- need to document semi-ring nonsense in docs
- need to write dissertation
- it would be really helpful to have a CLI tool so I could just run `compile` or `run` on a string to easily test.
- refactor viterbi.py to use numpy.

```bash
[atticusk@nixos:~/coding/part_ii_project]$ find PartIiProject -name "*.lean" -exec wc -l {} + | sort -nr | head -n10
  3987 total
   546 PartIiProject/Rust.lean
   494 PartIiProject/SyntaxSDQL.lean
   462 PartIiProject/Untyped/Infer.lean
   448 PartIiProject/Term2.lean
   316 PartIiProject/SurfaceCore2.lean
   302 PartIiProject/Term.lean
   302 PartIiProject/CodegenRust.lean
   216 PartIiProject/Untyped/ExtractLoads.lean
   147 PartIiProject/Untyped/TypeOf.lean
```

```
[atticusk@nixos:~/coding/part_ii_project]$ nix run .#performanceComparsion
trace: evaluation warning: 'system' has been renamed to/replaced by 'stdenv.hostPlatform.system'
path = /home/atticusk/coding/part_ii_project/.sdql-perf-out/sdql-rs-target/release/19eb69637db2c043path = /home/atticusk/coding/part_ii_project/.sdql-perf-out/sdql-rs-target/release/ad686ba0c2eda6c4path = /home/atticusk/coding/part_ii_project/.sdql-perf-out/sdql-rs-target/release/52d8caa4be80bdf4SDQL performance comparison (single run; wall-clock ms)
case                             sdql-rs      lean-gen     lean/sdql
--------------------------------------------------------------------
micro_sum_range_add                  1ms           1ms        1.000×
micro_sum_range_dict_build          21ms          93ms        4.428×
micro_sum_range_lookup               5ms          41ms        8.200×
tpch_q01                             1ms           1ms        1.000×
tpch_q02                             1ms           1ms        1.000×
tpch_q03                             1ms           2ms        2.000×
tpch_q04                             1ms           2ms        2.000×
tpch_q05                             1ms           2ms        2.000×
tpch_q06                             1ms           2ms        2.000×
tpch_q07                             2ms           2ms        1.000×
tpch_q09                            10ms           2ms        0.200×
tpch_q10                             2ms           1ms        0.500×
tpch_q11                             2ms           1ms        0.500×
tpch_q12                             1ms           2ms        2.000×
tpch_q13                             2ms           1ms        0.500×
tpch_q14                             1ms           1ms        1.000×
tpch_q16                             2ms           1ms        0.500×
tpch_q17                             1ms           2ms        2.000×
tpch_q18                             2ms           2ms        1.000×
tpch_q19                             1ms           1ms        1.000×
tpch_q20                             1ms           2ms        2.000×
tpch_q21                           702ms           2ms        0.002×
tpch_q22                             1ms           2ms        2.000×
tpch_q01_sf001                      30ms         237ms        7.900×
tpch_q02_sf001                       6ms          26ms        4.333×
tpch_q03_sf001                      38ms        5194ms      136.684×
tpch_q04_sf001                      44ms         224ms        5.090×
tpch_q05_sf001                      34ms        1336ms       39.294×
tpch_q06_sf001                      31ms         214ms        6.903×
tpch_q07_sf001                      38ms        2402ms       63.210×
tpch_q09_sf001                      47ms         992ms       21.106×
tpch_q10_sf001                      34ms        2286ms       67.235×
tpch_q11_sf001                       4ms          23ms        5.750×
tpch_q12_sf001                      38ms         364ms        9.578×
tpch_q13_sf001                       9ms         101ms       11.222×
tpch_q14_sf001                      32ms         204ms        6.375×
tpch_q15_sf001                      32ms         206ms        6.437×
tpch_q16_sf001                       6ms          98ms       16.333×
tpch_q17_sf001                      31ms         208ms        6.709×
tpch_q18_sf001                      38ms        1449ms       38.131×
tpch_q19_sf001                      31ms         210ms        6.774×
tpch_q20_sf001                      34ms         249ms        7.323×
tpch_q21_sf001                     781ms       25735ms       32.951×
tpch_q22_sf001                       7ms          34ms        4.857×
--------------------------------------------------------------------
TOTAL                             2108ms       41959ms       19.904×
```

```

case                             sdql-rs      lean-gen     lean/sdql
--------------------------------------------------------------------
micro_sum_range_add                  1ms           1ms        1.000×
micro_sum_range_dict_build          19ms          97ms        5.105×
micro_sum_range_lookup               9ms          39ms        4.333×
tpch_q01                            10ms           2ms        0.200×
tpch_q02                             9ms           1ms        0.111×
tpch_q03                             9ms           2ms        0.222×
tpch_q04                             1ms           2ms        2.000×
tpch_q05                             2ms           1ms        0.500×
tpch_q06                            10ms           1ms        0.100×
tpch_q07                            10ms           1ms        0.100×
tpch_q09                            11ms           3ms        0.272×
tpch_q10                             9ms           1ms        0.111×
tpch_q11                             8ms           1ms        0.125×
tpch_q12                             8ms           2ms        0.250×
tpch_q13                             9ms           1ms        0.111×
tpch_q14                             8ms           2ms        0.250×
tpch_q16                             8ms           1ms        0.125×
tpch_q17                             9ms           2ms        0.222×
tpch_q18                             8ms           1ms        0.125×
tpch_q19                             9ms           1ms        0.111×
tpch_q20                             4ms           3ms        0.750×
tpch_q21                           703ms           2ms        0.002×
tpch_q22                             9ms           2ms        0.222×
tpch_q01_sf001                      34ms         228ms        6.705×
tpch_q02_sf001                      27ms          26ms        0.962×
tpch_q03_sf001                      62ms        5248ms       84.645×
tpch_q04_sf001                      34ms         230ms        6.764×
tpch_q05_sf001                      54ms        1344ms       24.888×
tpch_q06_sf001                      29ms         207ms        7.137×
tpch_q07_sf001                      35ms        2407ms       68.771×
tpch_q09_sf001                      47ms        1055ms       22.446×
tpch_q10_sf001                      37ms        2345ms       63.378×
tpch_q11_sf001                       6ms          22ms        3.666×
tpch_q12_sf001                      37ms         357ms        9.648×
tpch_q13_sf001                       8ms         100ms       12.500×
tpch_q14_sf001                      32ms         206ms        6.437×
tpch_q15_sf001                      31ms         207ms        6.677×
tpch_q16_sf001                       6ms          97ms       16.166×
tpch_q17_sf001                      31ms         192ms        6.193×
tpch_q18_sf001                      38ms        1396ms       36.736×
tpch_q19_sf001                      31ms         200ms        6.451×
tpch_q20_sf001                      35ms         239ms        6.828×
tpch_q21_sf001                     773ms       24619ms       31.848×
tpch_q22_sf001                       6ms          35ms        5.833×
--------------------------------------------------------------------
TOTAL                             2276ms       40929ms       17.982×
```


Optimisation Performance Comparison:

```
[atticusk@nixos:~/coding/part_ii_project]$ nix run .#optimisationPerformanceComparison
trace: evaluation warning: 'system' has been renamed to/replaced by 'stdenv.hostPlatform.system'
SDQL optimisation performance comparison (mean of 3 run(s); wall-clock ms)
Params: dictN=200000, memoN=100000, memoM=1000
case                                   unopt           opt     opt/unopt
------------------------------------------------------------------------
vertical_loop_fusion_key_map           124ms          87ms        0.701×
vertical_loop_fusion_value_map         109ms          53ms        0.486×
horizontal_loop_fusion                  35ms          39ms        1.114×
loop_factorization_left                 31ms          32ms        1.032×
loop_factorization_right                34ms          31ms        0.911×
loop_invariant_code_motion              31ms          34ms        1.096×
loop_memoization_lookup               1409ms          29ms        0.020×
loop_memoization_partition            1399ms          40ms        0.028×
------------------------------------------------------------------------
TOTAL                                 3172ms         345ms        0.108×

```

 nix flake lock --update-input nixpkgs --update-input nix --update-input lean4-nix --update-input flake-parts

Interactive view
file:///home/atticusk/coding/part_ii_project/.sdql-flamegraph-out/svgs/

============================================================

Graph Reachability: SDQL vs Python (wall-clock ms)
case                             SDQL        Python   SDQL/Python
-----------------------------------------------------------------
reach_chain_10 (n=10)             2ms          22ms       11.000×
reach_chain_50 (n=50)             9ms          24ms        2.666×
reach_chain_100 (n=100)          43ms          24ms        0.558×
reach_chain_200 (n=200)         304ms          29ms        0.095×
reach_chain_500 (n=500)        5401ms          78ms        0.014×
reach_cycle_10 (n=10)             2ms          24ms       12.000×
reach_cycle_50 (n=50)             9ms          29ms        3.222×
reach_cycle_100 (n=100)          49ms          27ms        0.551×
reach_cycle_200 (n=200)         349ms          34ms        0.097×
reach_cycle_500 (n=500)        5808ms         112ms        0.019×
reach_star_10 (n=10)              3ms          25ms        8.333×
reach_star_50 (n=50)              7ms          22ms        3.142×
reach_star_100 (n=100)           29ms          27ms        0.931×
reach_star_200 (n=200)          226ms          27ms        0.119×
reach_star_500 (n=500)         4223ms          36ms        0.008×
-----------------------------------------------------------------
TOTAL                         16464ms         540ms        0.032×

Viterbi (max-product closure): SDQL vs Python (wall-clock ms)
case                               SDQL        Python   SDQL/Python
-------------------------------------------------------------------
viterbi_chain_10 (n=10)             2ms         133ms       66.500×
viterbi_chain_50 (n=50)            20ms         267ms       13.350×
viterbi_chain_100 (n=100)          77ms         205ms        2.662×
viterbi_chain_200 (n=200)         904ms         310ms        0.342×
viterbi_chain_500 (n=500)        9100ms        1468ms        0.161×
viterbi_cycle_10 (n=10)             3ms         131ms       43.666×
viterbi_cycle_50 (n=50)            14ms         116ms        8.285×
viterbi_cycle_100 (n=100)          70ms         129ms        1.842×
viterbi_cycle_200 (n=200)         460ms         414ms        0.900×
viterbi_cycle_500 (n=500)        6900ms        1023ms        0.148×
viterbi_star_10 (n=10)              2ms          90ms       45.000×
viterbi_star_50 (n=50)              8ms          85ms       10.625×
viterbi_star_100 (n=100)           61ms          98ms        1.606×
viterbi_star_200 (n=200)          263ms         100ms        0.380×
viterbi_star_500 (n=500)         4622ms         402ms        0.086×
-------------------------------------------------------------------
TOTAL                           22506ms        4971ms        0.220×
