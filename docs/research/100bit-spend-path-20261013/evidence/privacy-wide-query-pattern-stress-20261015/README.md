# Query-pattern rank stress (2026-10-15)

This is a finite rank diagnostic against one retained full-OS R1 S2 transfer fixture. Each run parses and validates the same proof/public input and derives its gamma, semantic alpha values, and circle challenges from that fixture. The three stress runs then replace only the 22 query indices used by the raw C1, H1, and pure-image rank calculations. These substituted query vectors are rank-stress inputs; they do not represent verified transcript outputs or a protocol security result.

The fixture is the retained 13-pair full-OS artifact with proof SHA-256 `86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c` and public ASF8 SHA-256 `f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`. The proof was read from the existing NUC `historical-reuse-task`; no task directory or wallet key was copied into this evidence bundle. `source/p3-inputs-sources.json` records the earlier P3 rank-gate fixture and is included only for its dependency-tree pins; its older proof hash is not the fixture used here.

The P3 rank-gate source set and `Cargo.toml`/`Cargo.lock` were pinned. The only source change is the isolated `probe.rs` query-pattern hook in `source/query-pattern-stress.patch`. It checks that every selected query vector has 22 distinct values in `[0, 2^18)`. Compilation attempt a failed with Rust E0282 because the local `collect()` result type was ambiguous; the exact failed source and log are retained. Attempt b adds the explicit `Vec<usize>` annotation and compiles successfully. Both used the release profile, locked offline dependencies, `private-leaf-salts`, and the pinned P3 dependency source tree.

| Query set | C1 ranks (16 lanes) | H1 rank / ambient | Pure image / silent rank | Exit | Wall |
|---|---:|---:|---:|---:|---:|
| Fixture queries (control) | 112 in every lane | 94 / 95 | 1080 / 1076 | 0 | 13.01 s |
| Consecutive `0..21` | 112 in every lane | 94 / 95 | 1080 / 1076 | 0 | 12.51 s |
| Upper boundary `262122..262143` | 112 in every lane | 94 / 95 | 1080 / 1076 | 0 | 13.51 s |
| Spaced `floor(i*262144/22)`, `i=0..21` | 112 in every lane | 94 / 95 | 1080 / 1076 | 0 | 13.51 s |

Every compile/run used a systemd cgroup with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. The exact command, cgroup peak, sampled RSS, wall time, and exit status are in the per-attempt/run JSON receipts. The optimized executable is archived as `target/probe.tar.gz`; its uncompressed SHA-256 is `b1dac9a044c258d2b502cdf248c115d1b70e8be1802a9c778a08a30e81af713c`.
