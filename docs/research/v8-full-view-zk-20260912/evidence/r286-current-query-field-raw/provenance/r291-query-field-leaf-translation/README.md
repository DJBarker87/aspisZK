# R291 QM31 query field leaf translation

The R289 retention candidate translated the exact R284 ordered LLBC successfully. The two requested bodies are present: `aspis_core::field::{aspis_core::field::QM31}::neg` (Fun 0) and `aspis_core::field::{aspis_core::field::QM31}::mul_m31` (Fun 1). Each has `is_opaque=false`. The complete emitted closure has 7 functions, 3 types, 1 global, and no trait declarations or trait implementations. The other functions are `CM31.neg`, `M31.neg`, `CM31.mul_m31`, `M31.mul`, and `reduce_u64`; the global is `P`. Exact IDs, source spans, generated names, statuses, and helper edges are in `inventory.json`.

The runner template produced namespace/subdirectory `AspisAspisR291QueryFieldLeaves` because its replacement doubled the `Aspis` prefix. The lead reviewed and accepted that exact spelling as the translation's provenance identity; no rerun was requested. A future raw adapter can place/copy the unchanged requested definitions under its own namespace while referring to the helper translation. The generated file bodies remain unmodified.

The frozen input hash is `37a693d55297515db02c3284f87226b8fc5f0df31cceeb3ec0d16460a69ddce5`; the R289 binary hash is `3c741510837e33e0debca5798fb46ae81861ec06d5d561b7975b16f5705e42e9`. Campaign revision recorded at launch: `380c7d46c9719dcfcab601fac2607861d47dee02`. The frozen LLBC root has no Git metadata.

Translation exited 0 under systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. `/usr/bin/time -v` reports 0.25 s wall, 58,960 KiB maximum RSS, and zero swaps; systemd reports 361 ms runtime, 359 ms CPU, and zero swap peak. R292 was separately reserved at 7 GiB, for 14 GiB aggregate maximum per the lead. Before/after host reservation snapshots and raw logs are retained here. No Lean compilation or axioms audit was run.

This is a mechanical declaration/body inventory only. It makes no source-correspondence or semantic claim.
