# R215 CopyNonOverlapping operand-visitation diagnostic

This scratch bundle records one isolated compiler experiment based on the R214 copied source/cache. The only source delta adds a `CopyNonOverlapping` match case in `decompose_global_accesses`: `src`, `dst`, and `count` each pass through the existing `visitor#visit_operand mk_unit_ty`; the statement is reconstructed intact. No interpreter, pointer, or memory semantics were changed. The unified diff records five added lines and no removed lines.

The ordinary copy included `_build`: 965 regular files (222,516,315 bytes), with no shared regular-file inodes. The recorded campaign identifier is lead-specified `9f15ca80a`; the copied Aeneas source snapshot itself had no captured Git revision. Parent `PrePasses.ml` SHA256: `92a8e2e8de4d8357acef2fe5c76f900aeb1d49588cfe15db9ba38d2ad2265e99`; patched SHA256: `b02ae350ea59d2f0a0029a5cab2cbecf253636835594309708fec2372206b7a5`.

The cached static Dune release build exited 0 (6.91 s, peak RSS 28,336 KiB, swaps 0). The binary SHA256 is `7e3be7b0c24975c248ad769c80bac2cc896a5f1b89c2858b8f01a6024cf80ae3`. Build and translation each ran in their own systemd scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; the Docker build container used 5g reservation, 7g memory, and equal 7g swap limit (no container swap). Host MemAvailable before/after build was 55,311,936/54,734,752 kB. Commands, launch descriptors, Docker inspect, cgroup properties, raw logs, and timing outputs are retained.

The unchanged R210 projection (SHA256 `b8ecd783e8c71da66dd929d43d7f5054521752fc7e111b2db102f16c5166fae5`) was translated once with the same flags. The translator exited 2 after 0.17 s (peak RSS 57,728 KiB, swaps 0). It reached type analysis and reported `Internal error, please file an issue`, Rust source `/rustc/library/core/src/option.rs:597:0-597:18`, Aeneas `TypesAnalysis.ml:229` (stack includes `analyze_full_ty`, line 274). No generated directory was produced.

This is diagnostic evidence only; it establishes no Lean vector theorem or source-to-model pointer/copy correspondence. No retry or Lean follow-up was run.
