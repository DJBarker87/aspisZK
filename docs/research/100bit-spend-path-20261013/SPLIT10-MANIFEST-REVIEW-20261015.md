# Split10 source-manifest and build fingerprint review

This is a read-only audit of the split10 SBF evidence. The candidate and baseline raw manifests each contain 754 entries. Removing 180 generated `target/` entries and one `.pyc` leaves 573 stable source/artifact entries per manifest. The baseline/candidate differ in exactly three stable source files, with all other stable hashes equal:

| Path | Baseline SHA-256 | Candidate SHA-256 |
|---|---|---|
| `programs/r1-cost-probe/src/lib.rs` | `66fcf176252443d0b3956797c8e854815cc8b6f8871a7cb5e246bea58dbf67fa` | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `c47518022dd264be14172e2ac4d31c0fcf86725030ca6500afac9c549d5bb8fa` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `tools/r1-cost-probe/src/bin/pool_gate.rs` | `b80b42e10de596ddc3510d225b46684b9791c9db5d0dccea53088a02eacf73e7` | `f8986a966a6b17340c84c8d6a3514eed061f25cba8f8d65433d458dc8f379406` |

At review time, worktree HEAD was `ce1fb7255213f5b390048d1ca709fea99176ae62`. All three intended candidate source files in the worktree match candidate hashes. Of the remaining 570 entries, 548 match the current checkout directly after excluding the three intended files; the full stable comparison is 551 matching, four hash differences, and 18 absent paths. The four differences are one test-only `crates/aspis-r1-cost-probe/tests/validated_prefix.rs` and three `docs/research/.../privacy-wide/{Cargo.lock,Cargo.toml,probe.rs}` files. The 18 absent paths are 15 files from three historical `privacy-wide-proof-rank` directories and three old root-level `r1-cost-probe` files. The machine-readable report gives every path/hash. These are checkout/history differences; the source manifests themselves show only the three intended source changes.

The recorded SBF invocation uses Solana `cargo-build-sbf` 3.1.13, platform-tools v1.52, features `pool-adapter,private-leaf-salts`, `--locked -j 2`, and a 4 GiB `MemoryHigh`, 6 GiB `MemoryMax`, zero-swap cgroup. The candidate SBF completed with exit 0. Input lockfile and manifest hashes, the exact command, cache path, and ELF hash/size are in `results/manifest-review.json`.

The baseline shared-point and split10 logs each contain 34 stack-offset diagnostics. Their ordered diagnostic lines are byte-identical after extracting those lines. This establishes that those emitted diagnostics match; the full logs differ. The split10 bundle retains the generic `llvm/bin/lld` driver pin and version output. The actual v1.52 linker is `/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld`, SHA-256 `2369c7b51282613ad9daf98d1c467c8cbef3b468e826c592e442b1d96958472b`, LLD 20.1.7 (commit `78496716176191b2dfb728e5e38501812e7467db`). This exact executable is recorded by the read-only preflight for the paired shared-point build, which uses the same pinned v1.52 platform-tools installation; see `evidence/shared-point-contraction-v152-20261015/results/preflight.txt`.

The build and source details are not a statement about protocol security or deployment readiness.
