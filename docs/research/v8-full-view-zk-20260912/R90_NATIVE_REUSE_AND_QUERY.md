# R86–R90: reconnect baseline winners, specialize preparation, source-bind q22

Base: `b1a0fdc499fdfa556c4c74cf7e4471bd7a1a15e4`, 2026-09-29.
Research branch `research/v8-r64-guarded-m31-20260929`.
**Neither under-1M execution nor full security is achieved.**

## Complete execution on the same two R84 proofs

| Experiment | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| Pushed R85 control | 1,199,479 | 1,197,630 | Control |
| R86: retained Merkle/leaf kernels | 1,187,578 | 1,185,776 | Retain |
| R87: shared preparation and fixed descriptor prefix | 1,143,400 | 1,141,596 | Retain |
| R88: eight-byte field alignment, based on R87 | 1,166,680 | 1,164,921 | Reject |
| R89: persistent packed private Q, based on R87 | 1,147,101 | 1,145,297 | Reject |
| R90: reconnect retained shared-gamma kernel to R87 | **1,141,057** | **1,139,217** | Retain research candidate |

R90 saves **58,422 / 58,413 CU** against the pushed control. The slower
fixture remains **141,057 CU over target**. Every measured honest execution
at the actual 1,000,000 cap exhausts; the complete accepted results above
use the diagnostic cap. Resource exhaustion is not called rejection.

All five completed variants pass the applicable actual-source differentials,
both honest host verifiers, 3,281 malformed-wire rejections plus one accepted
control, source-table export comparison and stack-safe SBF build gate.
Corrupted combined finals reject with Custom(6) at both caps, without resource
failure. Heap is unchanged at 262,144 bytes; simulated accounts are unchanged.
These are verifier-only executions, not settlement or an all-input CU bound.
The exact R84 fixtures were reused, not regenerated. R83 remains the selected
unchanged-profile control; R84 and its faster implementations are unpromoted.

## Native changes and retained checks

R86 reconnects the old `merkle-input.patch`: borrowed digest references and
SHA hashing of slices with exactly the same concatenated 53 parent bytes.
It also reuses `leaf_record::c2` on the existing contiguous C2/salt record.
Both roots, original packed bytes, canonical decoding, domain checks, exact
frontier consumption and final checks remain. The four old Merkle tests pass,
including the segmentation-sensitive negative backend. The standalone leaf
checker passes 160,000 byte/SHA comparisons. Existing `MerkleInput.lean` and
`LeafRecord.lean` results are reused at their stated source-shaped boundary;
no theorem about arbitrary segmentation-sensitive hash callbacks is inferred.

R87 shares the ordinary/first-point pair at code coordinates 0 and 1/2. The
actual map sends these to legal inactive rows 14, 15 and 30; pivot 1023 is
inactive. Factoring their tensor differences cancels the inactive constant
and shares the common high product. No division, challenge exception or
mask resampling is introduced. The old helpers and independent full dual are
retained: 128 paired comparisons cover both coordinate choices, in addition
to 64 full chord/image/final cases with arbitrary values.

The same change freezes only the **3,132-byte constant descriptor prefix**:
tag, 1,024 u16 permutation entries and 1,024 inactive bits. It is generated
from the exact source-export-checked tables. The host reconstructs and compares
the old bytes, and all variable inputs are appended at the same chronology.
No transcript byte or message changes. The combined 44,178 / 44,180 saving
has not been split into isolated attribution for its two edits.

R88 changes alignment only, retains sizes and wire serialization, and passes
the actual arithmetic/basis/opening checks. It nevertheless costs about 23.3k
more CU and is discarded. R89 changes private `Q` storage to two packed words,
retaining all canonical constructors and public field/decoder behavior. It
passes 1,593,216 private-operation comparisons plus the retained basis,
quotient, ordinary and wire tests, but costs 3,701 more CU and is discarded.

R90 reuses the old `shared_gamma.rs` **byte-for-byte**. The actual preparation
caller now computes its five independent 29-field batches together, sharing
28 nonconstant gamma powers. Host assertions compare all five outputs to the
original Horner calculations. The old arbitrary-five-row checker passes 2,048
cases and 580 basis cases, including canonical extremes and zero/one gamma.
The existing `SharedGammaDots.lean` integer bounds and independent-output
identity are reused; no new generic proof or privacy assumption is needed.
Its complete saving is only 2,343 / 2,379 CU against R87, not the old protocol's
25k result. Earlier CU figures are not transplanted to this source.

Early failures remain in the bundle: the old full host test target references
a missing `HOST_HASH` in unrelated test modules; the first leaf integration
omits its cfg; two preparation drafts misplace Rust inner doc comments or an
include. Corrected immutable stages follow. No failed build is a CU result.

## Exact executed instruction evidence

The R87 world-0 trace matches the clean **1,143,400 CU** and the deployed ELF's
text exactly. It contains 1,033,178 instructions, including 191,894 loads,
118,038 stores and 66,329 integer multiplies. General QM31 multiplication has
879 calls, with 810 distinct commutative operand pairs. The packed opening,
quotient kernel, semantic basis/dot and sparse G remain important native costs.
These are exclusive instruction counts, not additive inclusive CU intervals
or universal operand frequencies. Raw register traces stay on the NUC.

## Formal result: actual q22 inner loop

The pinned Charon/Aeneas tools extract the current Rust query sampler. The
only Rust edit is an appended public entry selecting count 22, bound 2^18
and draw cap 64. The actual sampler bodies remain unchanged.

Extraction exposes an unsupported standard-library primitive: the default
translation leaves `U32.is_power_of_two` opaque; including that body exposes
polymorphic `ctpop`. **Neither generated axiom template is admitted.** The
staged source is the exact generated prefix through the loop definitions,
with only import adaptation. The public argument-validation wrapper is
explicitly excluded and remains an obligation.

Three new proof leaves establish:

- Actual `contains`, four-byte word body and generated inner loop equal a
  finite typed scan, preserving early stops, duplicate handling and source
  counter/vector failure or divergence behavior.
- For initial count at most 22 and draws at most 64, this execution succeeds
  and equals the retained natural-number q22 scan. Counter addition and vector
  push are justified by explicit bounds, not assumed successful.
- The actual extracted loop therefore satisfies the scan's count/draw caps.
  A continuing scan consumes every supplied four-byte chunk. An empty chunk
  list does not itself detect completion, matching the source's boundary.

No randomness, fresh-oracle, honest-witness or successful-sampler hypothesis
is used. This is **not yet the complete q22 entry or query-history theorem**:
actual 32-byte chunk production, the outer squeeze loop, public guard and
shared-oracle observation composition are still separate work.

| Final exact target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| `AspisR86Query/Types.lean` | 0 | 1.21 | 2,538,724 | 0 |
| `AspisR86Query/Loops.lean` | 0 | 1.30 | 2,537,304 | 0 |
| `AspisV8R19/QueryChunkExecution.lean` | 0 | 2.21 | 3,698,376 | 0 |
| `AspisV8R19/QueryChunkModel.lean` | 0 | 2.37 | 3,715,420 | 0 |
| `AspisV8R19/QueryChunkSource.lean` | 0 | 2.03 | 3,689,908 | 0 |

Lean 4.32.0, exact base revision above, `lake env lean -j1 -M4500`.
354 compiled predecessors are reused; the final replay has 301 dependency
pins and 12 theorem audits. Nine use standard Lean axioms only; three also
retain the documented opaque `core.fmt.Formatter : Type`. No new axiom,
`sorry`, final warning, package-wide build or raised memory/recursion limit.
Failed focused elaborations and their resource logs are preserved.

## Evidence, resources and open gates

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r90_evidence.py
```

The public 345-artifact bundle pins source deltas, extraction inputs/output,
old reused kernels, completed and failed command logs, time/RSS/swap, resource
caps, fixture hashes, ELF hashes and complete runtime receipts. It contains
no wallets, proof fixtures, ELFs or raw register trace. No material is deleted.
All heavy jobs use the Tailscale NUC, release/offline/locked Rust and cached
Lean, with MemorySwapMax=0. High/max GiB are 5/7 host/Lean, 12/16 SBF,
2/3 runtime and 1/2 staging/analysis; reservations remain below 26 GiB.
The Solana skill's source → malformed-input → stack → full execution workflow
continues to determine selection, not operation counts.

The first profile security proposition remains **universal actual-source
C1/H1/G joint affine-image compatibility for R84**, including channel p0/p2,
all legal same-public witness differences and adaptive/degenerate prefixes
or explicitly justified exception losses. Two finite affine certificates
are not this theorem. Full causal posterior simulation, seed/commitment
shared-oracle composition, visible failure/retry/publication and coherent
pre-beta quotient-pair extraction remain open. No C1, one-swap H1 or other
negative regression is removed. No production promotion, deployment, wallet
operation, settlement execution, parameter reduction or security claim.
