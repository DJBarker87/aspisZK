# R73: generated squeeze framing and explicit oracle adapter

Base revision: `9ea038556c6ae2a9ffc89fe93107d947f0cd7b81` (R72).
Branch: `research/v8-r64-guarded-m31-20260929`.

## Exact proved boundary

The actual R72 generated `Transcript.squeeze_block` equals two sequential
calls to its supplied hash function: the old 32-byte state followed by byte
1, then the same old state followed by byte 2. The first answer is returned;
the second becomes the new state. This theorem keeps the backend arbitrary,
including internal failure and divergence. It does not assume random answers.
The source array allocation, slice copy, mutation and singleton hash framing
are reduced to this statement, not replaced by an assumed framing law.

A second leaf defines explicit byte/state conversions and a total hashv
adapter for an arbitrary deterministic function `H : Bytes → State`. Under
that constructed adapter, generated execution returns exactly the retained
`SourceDuplexStep.step` output and state. The two displayed hash input/output
pairs equal the retained model's `calls`. This last equality is not an
instrumented whole-program trace theorem or a proof of prover chronology.
Nor is the adapter a proof of concrete SHA ideality or a justification for
fresh independent answers at previously queried addresses.

There are 17 proved and axioms-audited theorems. Each uses only a subset of
`propext`, `Classical.choice`, and `Quot.sound`; no admitted proof, new axiom or
hiding assumption is introduced. These squeeze leaves do not depend on the
opaque formatter type. R72's separate inner-sampler `Formatter` dependency
remains recorded and is not erased by this result.

## Focused compilation and evidence

Lean `leanprover/lean4:v4.32.0`, pinned cached NUC workspace, `-j1 -M4500`.
Actual cgroup: `MemoryHigh=5 GiB`, `MemoryMax=7 GiB`, `MemorySwapMax=0`,
`TasksMax=128`. The one final replay reused 322 targets and compiled two;
289 dependency pins were checked. Source revision and hashes are in the
target metadata and `evidence/r73-squeeze/SOURCE_PINS.json`.

| Exact target | Exit | Wall seconds | Peak RSS KiB | Job swaps |
|---|---:|---:|---:|---:|
| `AspisV8R19/SqueezeSourceExecution` | 0 | 2.31 | 3,701,188 | 0 |
| `AspisV8R19/SqueezeOracleBridge` | 0 | 2.01 | 3,702,544 | 0 |

Focused unsuccessful attempts are retained: the squeeze proof first needed
explicit monadic lift simplification, then a symbolic length/take lemma. The
adapter proof first needed byte-name disambiguation and then symbolic
`List.ofFn` indexing instead of broad simplification. Corrected focused leaves
passed before the final replay. No higher-cap retry or package rebuild was
used. The evidence checker passes with 39 indexed artifacts.

## First remaining proposition

For each reachable actual inner-sampler state, prove safe four-byte slicing
and array conversion, exact little-endian decoding, masking and rejection of
P, and rollover at eight consumed words. Then prove the actual bounded
eight-attempt loop and mutable four-limb iteration preserve the decoded
values, advanced transcript state and oracle observations. Compose those
with the circle-map proof and existing outer retry theorem. The current
squeeze result does not discharge these propositions.

Shared-oracle/seed/C2 laws, complete joint-view causal simulation, visible
failure/retry/publication accounting and coherent pre-beta quotient-pair
extraction remain open. Full privacy and soundness are not claimed.

No Rust, verifier artifact, protocol, proof fixture or transcript change.
Retained complete CU: **1,495,663 / 1,497,050**; both actual 1M runs exhaust.
No unchanged SBF regression was repeated. No deployment or wallet operation.
