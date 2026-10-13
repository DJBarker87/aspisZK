# Sampler machine-bound arithmetic

`../../lean/SamplerMachineBounds.lean` proves the specified `P = 2^31 - 1` and `B = 2^32` Nat inequalities, reusing `R1SamplerLongDivision`. The statements cover the single-digit dividend, its quotient and remainder, a 256-bit rank divided by `P^8`, the `P^8 - 1` comparison, and the bounded digit-plus-addend carry facts. Small concrete powers are normalized as constants; no input enumeration or recurrence expansion is used.

The focused target compiled on the pinned NUC workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with `bash compile-one.sh R1SamplerMachineBounds a`. It exited 0 in 0.93 s, peak RSS 1,658,480 KiB, swap 0, with `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean threshold `-M5000`. `#print axioms` was emitted for all eleven theorems; each reported `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

Source SHA-256: `cb1d5e53fa26c968d16d84f4011747842c41d6a05c24bece76319f00023f54cd`. The imported `R1SamplerLongDivision.olean` SHA-256 is `de0c309055c4b765ae8821fd89f9f456fd2b0eeefb060d704b41d8985560c890` (source SHA-256 `6b0a35daf77c00c8cb45fe627b0e4fbdf07f50da714a3737dc045939f790ed8c`). The focused receipt, output, timing record, source-hash record, and compiled object are archived in `remote-evidence/`.

These results are Nat arithmetic only. They do not prove the correspondence of fixed-width arithmetic, shifts, casts, or byte assembly in the Rust source.
