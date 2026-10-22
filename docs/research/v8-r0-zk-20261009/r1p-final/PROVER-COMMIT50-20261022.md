# Part 50: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit50-20261022`.
Authorized Lean budget: J10200–J10299 only. Work proceeds through the six
interfaces in part 49, stopping at native payload equality, before any
FSExperiments conversion or joins.

## Frozen inputs and scope

Task base is recorded in `evidence/prover-commit50-20261022/pins/revision.txt`
under `docs/research/100bit-spend-path-20261013/`. No shipped file is changed.
Retained release ELF pins: default 40dc7574…, devnet 12cb0bc2…, Pool 121f3e29….
No fresh ELF build is claimed. Shipped code is never extracted by Aeneas;
independent owners and native transition gates provide the binding route.

## Endpoint before/after

The entire deployed endpoint is preserved verbatim in `endpoint/before.lean.txt`
and `endpoint/after.lean.txt` in this task's evidence. The snapshots are identical.
`RustProverRefinement` remains an explicit premise, with unchanged x/rust
quantifiers, failure event, conclusion and bound. No premise removal is claimed.

## Validation

Focused Lean targets run only on the build host, one module per attempt.
All host tools use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Rust uses four jobs, release optimization, and
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.
Exact source hashes, dependency fingerprints, target/status/wall/RSS/swaps,
source attribution and printed axioms are retained per attempt.

## Stage 1: component preparation and complete three-product value

J10203 proves `Prepare50.q`: all nine prepared coordinates are canonical and
are precisely the symbolic tower components, including CM `a+b` and QM
`c0+c1`. J10206 proves every entire three-input scalar accumulation and the
complete nine-total matrix. J10209 proves `Dot50.exact_result`: the independent
owned caller succeeds, returns canonical QM31, and decodes to
`∑ i : Fin 3, decode (x i.val) * decode (y i.val)` for arbitrary canonical inputs.
No prepared-coordinate, accumulator, or output/model identity is a premise.

Native preparation and all-27-product aggregation gates pass, with complete
output matrices; preparation also checks paired arithmetic operands and order.
The aggregation products are arbitrary bounded callee answers. Their integer
multiplication and canonical bound are separately proved by the retained
`NativeSquare49.mul64` and `ChannelSum49.product_bound`. This composes retained
part-49 channel transition/reconstruction gates with the new value proof;
it does not prove equality of the reordered complete caller's timing trace.
The prepared-multiplier path needed by the next interface remains next work.

J10200 was refused before compilation by the copied launcher's old range guard;
it is retired. The launcher now accepts only J10200–J10299 and retains global
Lean serialization and the 6G/8G/0/64 caps. J10202/05/08 are rejected carrier,
array-size inference and literal-index drafts; their replacement sources pass.
All accepted axioms are subsets of `[propext, Classical.choice, Quot.sound]`.
Focused receipts in `lean/attempts.json` record exact source attribution,
source/dependency fingerprints, target/status/time/RSS/swaps and axiom lines.
No shipped file changed; no deployed endpoint premise is removed.
