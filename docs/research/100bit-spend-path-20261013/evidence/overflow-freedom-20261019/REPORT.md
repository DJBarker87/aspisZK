# Stage-1 overflow-freedom: focused proof replay and remaining source frontier

Branch: `codex/r1-overflow-free-20261019`. Task base: `f9016d0a2`.
Historical handover commits: `93f5025d9`, `9d906cec2`.
The 2026-10-20 resume removes the obsolete environmental blocker and produces
fresh focused Lean receipts. **R22 remains open**: this packet must not be
used as a whole-deployed-verifier overflow-freedom certificate.

## Execution and evidence

The revised binding `local-lean.txt` permits compilation while holding
`/tmp/aspis-local-lean.lock.d` and with no other `lean -M4400` process running.
It does not use the old free+inactive >=10 GiB test. The launcher uses Lean
4.32.0, `-j1 -M4400 -DElab.async=false`, `/usr/bin/time -l`, and the private
`/tmp/r1-overflow-free-20261019-objects` directory. Shared lock waits are outside
the measured compile wall time. No existing Lean source or shared object was
edited, and no resource limit was raised.

`manifest.json` retains all historical and new attempts. Each receipt records
source revision/hash, direct import hashes/fingerprint, command/search path,
exit, wall time, peak RSS and swap readings. `dependency-snapshot.json`
also records the final read-only dependency layout, including public imports;
original per-attempt fingerprints remain untouched. Raw `out.log` and `time.log` files
are retained. `axioms-audit.json` parses complete multiline `#print axioms`
reports; only successful attempts count. Failed elaborations may print
`sorryAx` because Lean reports an incomplete declaration; these are excluded
from accepted proof evidence. No source contains a proof placeholder.

Missing focused dependencies were rebuilt in the private object directory.
`cache-overlay.json` records links to unchanged cached namespace objects,
needed because Lean selects the first package directory even when the
requested child object is missing there. This is cache reuse, not a coherent
release rebuild of the full verifier closure.

## Freshly replayed prior results

The six prior scalar/field modules all compile: `CheckedWrappingScalarAgreement`,
`R22CanonicalM31AddSub`, `R22CurrentReducerMul`, `R22CanonicalCM31`,
`R22CanonicalQM31`, and `R22FastPairingPrimitiveBounds`. Their exact domains
remain unchanged: canonical inputs for add/sub/tower operations, unrestricted
stored U64 for reduction, and unrestricted stored U32 for widened products.
Successful-checked-to-wrapping equality is paired with their totality lemmas;
it is not used alone to infer deployed totality.

Fresh compiles also cover emitted semantic add/mul, boundary and Horner
wrappers; bounded rho push body, full push loop, flush and nonflush outer
branches; the source-shaped all-prefix residue invariant; and the seven-batch
fast-dot actual reducer composition. The strict parser's
`ActualDecodeKStrictQM31Parser.source_refines` and
`success_has_strict_limbs` also have a fresh receipt.

`R22FastPairingRawRanges` now compiles unchanged: both partial folds are at
most 3P, and all ordered raw-coordinate additions/subtractions fit U64 under
the canonical product bound, including the pre-subtraction intermediates.
It is a Nat arithmetic theorem about the actual source formulas, not an
extraction/refinement theorem for private `Q`.

## New per-function results

All names below are under `AspisR1`. Exact anchors and receipts are also in
`theorem-index.json`.

| Theorem | File:line | Established domain/output |
| --- | --- | --- |
| `R22DecodeValueTotal.size_guards` | `lean/R22DecodeValueTotal.lean:36` | outer end bound implies all value stride/read/error-index bounds |
| `R22DecodeValueTotal.decode_value_total` | `lean/R22DecodeValueTotal.lean:44` | actual selected decoder is `.ok out`, with either Rust success or Rust rejection; explicit framing and size premises, no successful-decode premise |
| `R22DecodeLoopTotal.decode_loop_total` | `lean/R22DecodeLoopTotal.lean:12` | actual complete loop terminates without Aeneas failure, including noncanonical-byte rejection; payload/end bounds and byteOffset=32*offset are premises |
| `R22BatchedPushTotal.push_total` | `lean/R22BatchedPushTotal.lean:15` | actual outer push is total for either phase and preserves terms; canonical operands, in-bounds row and pending-product range are premises |
| `R22BatchedValueTotal.reducer_eq` | `lean/R22BatchedValueTotal.lean:14` | definitional equality of the two retained reducer emissions |
| `R22BatchedValueTotal.value_total` | `lean/R22BatchedValueTotal.lean:22` | actual value accessor is total on every in-bounds row for unrestricted stored U64 lanes, with four canonical output limbs |
| `R22ControlBounds.*` (eleven lemmas) | `lean/R22ControlBounds.lean:10` | source-shaped round/prepare tags, Horner/boundary indexes, dot/tail byte offsets, weights digits/point indexes and sampler dividends; not source-loop correspondence |

The decoder proof uses a generic `read_offset` lemma to keep each arithmetic
obligation small. An early monolithic attempt hit the default 200,000-heartbeat
limit; the replacement factors the proof rather than increasing that limit.
The final proofs use no `sorry`, `axiom`, `admit`, `native_decide`, or new
recursion/heartbeat overrides. There are twenty new proved declarations in this
resume, plus the two previously uncompiled raw-coordinate declarations.

## Final focused verification

There are 36 successful focused targets and 159 axiom reports from successful
attempts. The new combined `R22OverflowAudit` compiles once: exit 0,
8.645 seconds, peak RSS 3,208,069,120 bytes, 0 process swaps, 50 complete public
theorem axiom reports. Every accepted axiom set is a subset of
`{propext, Classical.choice, Quot.sound}`. The maximum RSS of a successful
focused compile is 3,224,158,208 bytes (`R22DecodeLoopTotal`). No OOM occurred.

The manifest retains 53 attempts: 36 successful targets, 16 failed attempts,
and the historical refused memory preflight. Failures include a launcher root
error, absent cached dependencies, and repaired decoder elaboration/heartbeat
errors. One exploratory, unused raw `AspisR1CandidateParser.Funs` extraction
cannot compile standalone because it lacks the `Option Infallible`
discriminant instance. It was not changed or used: the actual strict parser
proof consumes the retained standalone `R1CandidateFieldParsers` facade and
now compiles successfully. This failure is kept rather than treating that raw
file as a verified dependency.

`operation-census.json` retains all 6 pinned inputs and all monadic bind lines;
its source-hash/census check passes again. The 24 exact integer envelope checks
also pass. Those checks are Python arithmetic, not a Rust execution test or a
Lean source-refinement proof. No Rust, SBF, full release-manifest replay,
deployment, push, or merge was performed.

## Findings and exact remaining obligations

No overflow counterexample on an admitted input was established. This does
not establish that none exists. Arbitrary direct noncanonical/unbounded helper
calls can overflow; they are not silently admitted by these theorems. No Rust
wrapping/checked policy was changed.

The original requested all-cone conclusion is still unproved:

1. The pinned extraction set does not contain the optimized current
   `weights`, private `fast_pairing::Q`/dot, or `fast_dots` bodies. Their source
   arithmetic envelopes and symbolic bounds are available, but an actual
   emitted-body theorem cannot be stated against absent definitions. Re-emit
   and re-pin those bodies and their library operations (S1/S3/S4/S5/S7/S9). The lexical
   `extraction-frontier.json` check found no matching deployed-body
   declarations across 3,770 checked Lean sources; this is not a claim that
   generating them is impossible.
2. Compose total ten-round and prepare orchestration, including actual
   serialization, transcript/sampler, query and claim children. The historical
   prepare model has explicit boundaries and a stale claim signature;
   success inversion cannot discharge totality.
3. Connect outer `decode_k` checked size/slice guards and framing to the new
   complete-loop theorem. Existing success-canonicality theorems and the strict
   codec supply output facts after successful decode; caller propagation still
   needs composition.
4. Connect the global rho cadence, selected distinct row traversal, vector
   length and canonical power/basis selection to `push_total`; the function
   itself intentionally does not increment terms. Reuse the stronger existing
   loop/flush range and residue theorems for the caller invariant.
5. Derive deployed wrapping acceptance => checked/model acceptance on one
   coherent release closure. Focused cache-based compiles are not that release
   result. Stage 2 waits for its extraction; replacement parser and Merkle
   path code remain expressly excluded.

The remaining blocker is a source/extraction and composition frontier, not the
obsolete local memory/lock policy. No whole-verifier or release claim is made.
