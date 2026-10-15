# WideExact parser differential

This host-only test invokes `WideExact::from_le_bytes` from two actual full field modules: the baseline is the current `field.rs` plus unchanged `wide_exact.rs`; the candidate is the same full `field.rs` plus the isolated `WideExact::from_le_bytes` candidate from `wide-parser-extraction-20261015/input-b`. It compares panic, `None`, and returned eight-limb values and rejects panic outcomes on every vector. Canonical limb vectors must return their exact limbs.

The deterministic coverage includes input lengths 0–64, every byte value at each of the 32 positions in a 32-byte frame, all six boundary values independently at all eight limbs, all pairwise boundary combinations across limb-position pairs, 256 seeded random vectors at every length, and 4,096 canonical eight-limb inputs. The test is a finite differential check and does not prove equivalence for all byte strings or establish source/compiler correctness.

The optimized focused run uses the pinned `nightly-2026-06-01` rustc, `-C opt-level=3`, `-C overflow-checks=yes`, and a 4 GiB `MemoryHigh` / 6 GiB `MemoryMax` / zero-swap cgroup. Run and resource results are recorded below after execution.

**Result:** the focused optimized NUC run passed: 1 test, 30,055 input vectors, and 60,110 parser calls. Both parsers returned no panic for every tested vector, outcomes matched, and each of the 4,096 canonical vectors decoded to exactly its input limbs. The finite test does not establish equivalence over all possible inputs.

The pinned compiler was `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM 22.1.6. Compilation took 4.95 s with peak RSS 290,944 KiB and zero swap; the test took under 0.01 s with peak RSS 2,816 KiB and zero swap. The cgroup was `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Exact commands, outputs, timing logs, source snapshots, and the compiled test binary are retained in this directory and `inputs/results/`.
