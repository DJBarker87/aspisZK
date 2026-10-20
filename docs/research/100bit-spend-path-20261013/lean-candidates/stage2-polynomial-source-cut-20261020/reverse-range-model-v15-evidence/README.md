# Reverse-range model V15 corrected-run evidence

This is the environment-corrected focused rerun of the exact V14 Lean source. V14 used the Lean default memory option; V15 uses the standard runner with `-j1 -M 4400`, a fresh admission, `MemoryHigh=1 GiB`, `MemoryMax=2 GiB`, and `MemorySwapMax=0`. No theorem source changed. The result is exit 0, 2.207 seconds, process peak RSS 4,007,716 KiB, cgroup peak 373,014,528 bytes, scope swap 0, and no memory events.

The imported unrolled consumer direct object is pinned by `proof-evidence/preflight.json`. Axiom output is preserved in `proof-evidence/lean.log`: `rangeRevIndices_zero_seven` and `boundedReverseRangeResult_zero_seven_eq` are axiom-free; the current-consumer composition depends on the standard `propext`, `Classical.choice`, and `Quot.sound`. This model does not prove Rust `Rev<Range<usize>>::fold` correspondence.

No OLean or other compiled binary is included. `manifest.json` hashes every included file.
