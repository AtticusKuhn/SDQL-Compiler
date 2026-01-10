
- The implementation of `concat` in Rust is ugly, need to fix it.
- `sub` currently type `t -> t -> t`, should introduce a typeclass for it.
- Get github workflow to run successfully.
- Make `<` and `<=` and `==` use a typeclass (instead of taking in any type `t`)
- We currently use a bad representation of dates (i.e. YYYYMMDD as an `i64`). This is dumb.
Q15 is tiny-only (SF=0.01 currently diverges due to missing
    promote[max_prod]/max-semirings).
- get rid of ugly `A *{Type} B` syntax
- Get rid of ugly `<_1 =..., _2 = ...>` syntax. Just replace this with `<..., ....>`
- the tuple_add4, tuple_add5 thing is annoying. Just replace with a macro.

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
