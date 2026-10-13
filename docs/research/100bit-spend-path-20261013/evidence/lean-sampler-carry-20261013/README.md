# Sampler carry arithmetic focused Lean result

`R1SamplerCarry` proves that for `N ≥ 2`, `q < N - 1`, and `r < N`, the
conditional result `s` when `s < N` and `s - N + 1` otherwise, with
`s = r + q + 1`, equals `((q * N + r) % (N - 1)) + 1` and lies in `(0,N)`.
It also proves that the wrapped value `s - N + 1` is below `N`. This is a
symbolic natural-number identity only; it does not identify Rust digits,
loops, or sampler behavior and makes no probability/security claim.

Final source:
`docs/research/100bit-spend-path-20261013/lean/SamplerCarry.lean`, SHA-256
`cb56f879bd84899100f3755d6cb43db8aa333da3ae9944956118c1713fd913d8`.
Focused target `R1SamplerCarry` compiled in pinned workspace
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with
`compile-one.sh R1SamplerCarry d`. Attempt d exited 0 in 0.51 s, peak RSS
809,224 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`,
`MemorySwapMax=0`, and Lean threshold 5000 MB. Both theorem axiom lists are
`[propext, Quot.sound]`. Object:
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects/R1SamplerCarry.olean`.

Attempts a–c are retained with their exact source hashes, logs, and timing
receipts; they exited 1 during algebraic proof plumbing. Attempt d is the green
result. Workspace source revision:
`3638d7546f6e03a1afb0eaabdb1cff38d1631e84`; the final dirty-source hash
identifies the compiled file.
