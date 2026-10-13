# Sampler digit arithmetic focused result

`R1SamplerDigits` defines `lowValue p n x` by recursive quotient/remainder
and proves (for `0 < p`) its quotient decomposition, the bound
`lowValue p n x < p^n`, and equality with `x % p^n`. These are symbolic
natural-number statements only; they do not identify Rust digits or loops,
fixed-width arithmetic, or any probability/security property.

Final source: `lean/SamplerDigits.lean`, SHA-256
`63f68242e997faf598724e969130acd60085382c673c60d2819cbfbc19b67ed9`.
Base revision: `a7ff42dc8068119ba1aea4e7bda471a01177b5be`.

The focused compile ran on the pinned NUC workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1SamplerDigits e`. Attempt e exited 0 in 0.81 s, peak RSS
1,610,712 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0` and Lean threshold 5000 MB. The `#print axioms` results are
`[propext]` for `lowValue_decomposition` and `[propext, Quot.sound]` for
`lowValue_lt_pow` and `lowValue_eq_mod_pow`. The object is
`objects/R1SamplerDigits.olean` in that workspace.

Attempts a–d are retained with their exact source hashes, logs, timing logs,
and receipts. Attempt a stopped at a missing cached `Mathlib.Tactic.Omega`
object; b–d exposed proof-plumbing issues and were superseded by changed
sources. Attempt e is the final green result. The copied receipt for each
attempt records the source hash used for that run.
