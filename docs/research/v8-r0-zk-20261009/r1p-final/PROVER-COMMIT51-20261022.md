# Part 51: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit51-20261022`.
Only J10300–J10399 are authorized. No shipped crate or program file is changed.

## Endpoint before/after

Verbatim endpoint snapshots are in `evidence/prover-commit51-20261022/endpoint/`
under `docs/research/100bit-spend-path-20261013/`. They are identical to part 50.
`RustProverRefinement` remains explicit, with unchanged quantifiers and bound.

## Stage 1: duplicate declaration ownership

`Linear50` imports `Batched48` and reuses its byte-identical CM31/QM31
`mul_m31` definitions. No Session A module is edited. The replacement binder
checks the extraction bodies against that single retained owner so regeneration
preserves the fix. The six affected targets are rebuilt in J10300–J10305;
the combined audit is J10306. Shared sources and objects are snapshotted in the
branch-named host workspace before replacement. All needed dependents are
rebuilt with new dependency fingerprints.

Exact targets, source revisions/hashes, dependency fingerprints, exit status,
wall time, peak RSS, swap and full printed axioms are recorded in
`lean/attempts.json` and `lean/receipts/` in that evidence directory.
All jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Lean retains the 7000 MiB internal limit. No cap increase is used.

## Stage 2: symbolic caller split

The old J10298 failed at `ProverCommitMaskArithmetic50.caller` with kernel
excessive memory consumption: exit 1, 19.10 s, 7170376 KiB, zero swaps.
The replacement first proves `ProverCommitBind51.three` over an arbitrary
carrier and arbitrary Result-valued callees. Concrete source conversion,
array construction, and all three callees are locally opaque at the composition
boundary. No large computation is reduced; the existing individual arithmetic
proofs are reused. `ProverCommitMaskArithmetic51.caller` keeps the exact old
coefficient-law premise, input quantifiers and conclusion. It passes J10311:
exit 0, 1.82 s, 4046236 KiB, zero swaps, standard axioms only.
J10307/08 are rejected symbolic let-normalization drafts; J10310 proves the
corrected helper. J10309 is retired before compilation (missing dependency
object). The coefficient producer remains the next obligation; this conditional
caller is not complete native selected-mask success.
