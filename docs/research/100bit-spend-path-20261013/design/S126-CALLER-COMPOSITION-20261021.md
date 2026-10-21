# S1 / S2 / S6 current compact caller composition — 2026-10-21

**Target not yet established. S1, S2 and S6 are not closed as actual SDK-to-release cones.**
This is an additive proof/source-cut packet, not a production verifier change.

## Freeze and scope

- Authoritative verifier source: `b2727acd3abf79315d18b754a260f58f4b1c6326`.
- Research parent: `d8fc9db732c70ef8dd1dd548184326318d5e1ad1`.
- Isolated branch/worktree: `codex/s126-caller-20261021`, `.worktrees/s126-caller-20261021`.
- Compact QM31, depth-18 binary multiproof, two verification/settlement transactions;
  transparent and trusted-setup-free; no grinding/work-normalization credit.
- Consulted OVERNIGHT, R22-TOTAL, REPIN-s2, REPIN-s6, S1 next-freeze handoff,
  S1 claim-trace status, their addenda, and the current Session A handoff.
- The admitted compact route is `candidate::tx1 → candidate::prepare → Prepared::new`.
  Historical `tx1_prepare` is on the audit-only eight-way route. A theorem about
  that route cannot substitute for compact execution.
- S3/S9, S4 and S5 source/proof tracks were not modified. Their retained prepared
  and codec lemmas are imported where stated; importing them is not new closure.

## Enclosing obligations actually proved

All Lean paths below are in `lean-candidates/s126-caller-boundary-20261021/`.

1. **TOTAL contextual decoder reuse:** `S6DecoderScopedReuseV1.decoder_scoped_reuse`
   eliminates the separate decoder-success premise inside the actual decoder's
   own scope. Both complete Results agree with the identical arbitrary downstream
   continuation. Decoder failure/divergence, Rust rejection, and downstream errors
   are preserved. `decoded_scope_success` derives the decoded statement and exact
   child call, including release observer `None`, from one enclosing success.
   The arbitrary continuation is explicitly not a translated AccountInfo stage1.
2. **ACCEPTED-ONLY current compact preparation reachability:**
   `PrepareReachability.prepare_success` derives actual View parsing, semantic
   verification and Prepared.new success with the same input/output scratch from
   successful emitted compact prepare. The old separate View, semantic-result and
   Prepared.new success witnesses are conclusions, not assumptions.
3. **ACCEPTED-ONLY compact tx1 reachability:**
   `Tx1Reachability.tx1_prepared_new` additionally derives the real split guard,
   zero/allocation/preparation path, and complete successful-preparation suffix
   (including nested errors and checkpoint operations). `afterPrepare` is a
   verbatim emitted suffix, not an acceptance-only stub.
4. **ACCEPTED-ONLY first-to-current-tx1 composition:**
   `FirstComposition.first_current_prepared_new` takes one enclosing firstCurrent
   success and derives actual decode, the exact full public statement passed to
   semantic verification, same original public/proof bytes and k, None observer,
   same View/Verified/Prepared.new/scratch and full tx1 suffix. The two public-carrier
   maps copy every field and have inverse theorems for both variants. The decoder,
   child, View, semantic result and scratch are no longer independently supplied
   success premises. Child operations and digest/error implementations remain
   explicit typed parameters; their concrete installation is not assumed proved.
5. **TOTAL constant/checked arithmetic leaves:**
   `ConcreteConstants.constants_total`, `zero_total`, `source_ranges` prove exact
   checked Usize computations and WideExact zero. `first_with_constants` installs
   seven source leaves into the enclosing first theorem: QM31.ZERO, CodecError→Parse,
   HEADER=16, COMPACT_SEMANTIC=7015, COMPACT_Y1=464, SEMANTIC_BYTES=13831,
   OFF_ROUND0=7527. Derived offsets/lengths are OFF_Y1=7031,
   OFF_INACTIVE=7495, LOGICAL_Y1=928, allocation=14759,
   OFF_FOLDED_ROOT=7751, OFF_ROUND1=7783. This does not prove allocation or all child
   arithmetic total. `source-constant-pins.json` checks the frozen Rust expression
   DAG, checked intermediate ranges and exact zero/error constructor bodies.
6. **TOTAL rejection:** `ReleaseReject.tx1_bad_split` proves complete rejection
   before child operations for k≠10; the enclosing first_decoded mapping preserves
   that rejection. `eleven_rejected` records the real adapter/verifier mismatch:
   the adapter admits k=11 at its range guard, while compact tx1 rejects it. No
   admissible input was silently removed to obtain the result.

## Exact remaining child boundary

`CurrentCompactCallerModelV1.Ops` retains every external operation's original
signature. It introduces no custom axioms. Before constant installation there
are 22 fields. Seven are concretely fixed above. The remaining 15 are:

| Field | Frozen source operation |
| --- | --- |
| op1 | heap.filled, with allocation errors |
| op3 | parse_shape |
| op4 | canonical_scan |
| op5 | wide_view |
| op6 | batch_merkle |
| op7 | query_loop |
| op8 | Prepared::new, complete result and mutable scratch |
| op9 | semantic.verify_observed |
| op10 | compact.expand_semantic |
| op11 | compact.expand_values |
| op16 | checkpoint |
| op17 | BatchedWeights.finish |
| op18 | BatchedWeights.new |
| op19 | QueryGeometry.for_range |
| op20 | Accumulator.new |

Theorems quantify over these complete operations. There is no hypothesis that
errors cannot occur or that all callbacks are total. Success permits deriving
only operations reached by that run. Concrete instantiation/refinement remains
necessary; bundling callbacks into Ops is not claimed as premise discharge.

## Actual SDK and original Prepared source work

`tools/s126-sdk-20261021/prepare.py` cuts the exact frozen stage1 and four account
guards without body rewrites. It uses the real SDK AccountInfo/Rc/RefCell, real
ProgramError and full actual public structs. Explicit decoder/validator/encoder/
tx1 boundaries are harness code, not source-correspondence proofs.

- The bounded `sdk_immutable_alias_and_writeback` Kani check passed for arbitrary
  16-byte contents, real cloned AccountInfo borrows, borrow conflicts and writeback.
  This is a bounded SDK fact, not a universal account theorem or stage1 closure.
- Full SDK stage1 `sdk-v1` timed out at 600s. The narrowed v2 binding run was
  voluntarily stopped after 415s of monolithic CBMC work. The address-correspondence
  v3 run also timed out at 600s. All unsuccessful receipts/logs are retained.
  No result from those runs is promoted to a theorem or counterexample.
- Charon/Aeneas successfully emitted the actual original Prepared.new body in
  `prepared-v7`, with real concrete carriers and transcript state. Its raw output
  is retained as unimported provenance. Extraction success is not a proof of its
  equivalence to the installed retained prepared model or nested-claim fission.
- `CurrentCompactInstalledPreparationV1` is a separate installed-backend candidate.
  Its `first_installed_claim_and_rank` theorem compiled successfully (30.728s,
  peak RSS 3394011136 bytes, zero swaps; only the three standard axioms). It
  derives canonical gamma/kappa, OriginalPayloadClaimMeaning and JointRankTrace
  from one firstCurrent success with the retained backend installed. The full
  carrier maps preserve every field. This is an enclosing installed-backend
  theorem with sampling/embed parameters, not a concrete-source installation.
  It must never be used as evidence that the original Prepared.new or SDK stage1 instance has been proved.

Still required for whole-cone closure: actual stage1/account/borrow/state/error
refinement and the actual first/first_decoded adapter binding; original Prepared.new
full-result/scratch/transcript correspondence to the retained claim/powers model;
original nested-claim versus fission equivalence and P6/RustStd boundary; relevant
child range/totality obligations and concrete release artifact installation.
Other tracks' operations above remain owned by those tracks.

## Validation and trust boundary

Evidence is source-only `focused-extractor-proof-packet-v1` under
`evidence/s126-current-caller-20261021/`. Each launched attempt records target,
source/tool/direct-import hashes, command, exit, wall, peak RSS, swaps and axioms.
NUC attempts have fresh admission and MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0. Local Lean uses one atomic owned lock, -j1 -M4400.
Failed attempts are retained and excluded from accepted evidence.
An early successful compile used a cached nonstandard Formatter axiom and is
**rejected**; accepted callers were recompiled using the retained repaired
Formatter source/cache. Accepted audits allow only propext, Classical.choice,
Quot.sound (or no axioms). No sorry/custom axioms/native_decide/resource overrides
were added to accepted proofs. Cached focused checks are not a coherent release
rebuild. No unchanged full replay, SBF rebuild or production-source repin ran.

Generated discriminant instances are qualified, with identical constructors and
codes, to avoid collisions with retained source modules. External operation
axioms in raw generated templates are never imported: they become explicit Ops
fields. Raw generated text is provenance, not accepted proof source.

No new frozen-source decision is required for these additive proofs. Adopting
any prepared fission/decoded-reuse source candidate still requires the full
semantics/equivalence gates and explicit source/tool/artifact re-pin. No claim is
made that ≤2^-100 per-attempt soundness is established by this packet.

## Accepted focused targets

`accepted-targets.json` selects successful receipts matching the current source
and focused object hashes; failed or superseded attempts remain diagnostic only.
`selected-import-pins.json` records exact selected transitive object hashes and
module imports, without distributing compiled objects. `formatter-repair-pin.json`
identifies the existing repaired Formatter source. `check-packet.py` verifies the
reversible emission adapter, complete tx1 suffix, current source receipts,
standard-axiom audits and source-only file discipline. It is not a proof of the
unclosed implementation instances.

| Target | Wall seconds | Peak RSS bytes | Swap |
| --- | ---: | ---: | ---: |
| CurrentCallerUsizeArithmeticV1 | 3.499 | 2243379200 | 0 |
| CurrentCompactCallerConstantsV1 | 4.052 | 3285434368 | 0 |
| CurrentCompactCallerModelV1 | 4.618 | 2264170496 | 0 |
| CurrentCompactCallerTypesV1 | 4.378 | 2282962944 | 0 |
| CurrentCompactFirstCompositionV1 | 51.825 | 2720448512 | 0 |
| CurrentCompactInstalledPreparationV1 | 30.728 | 3394011136 | 0 |
| CurrentCompactPrepareReachabilityV1 | 3.712 | 2263023616 | 0 |
| CurrentCompactReleaseRejectV1 | 9.430 | 3202809856 | 0 |
| CurrentCompactTx1ReachabilityV1 | 2.859 | 2262253568 | 0 |
| S6DecoderScopedReuseV1 | 10.427 | 3278438400 | 0 |

The retained extraction workspace was compared byte-for-byte against all 226
tracked files in the four relevant source/package trees at the frozen revision;
all matched (`extraction-source-freeze.json`). SDK tool hashes were collected
after the runs and are labelled retrospective; historical commands/versions and
exact per-run source hashes remain in the original receipts/inputs.

## Active continuation: S2 first, modular SDK and owned reference

The goal remains active. This is a checkpoint of continuing proof work, not
completion of S1/S2/S6. The authoritative source freeze remains
`b2727acd3abf79315d18b754a260f58f4b1c6326`. No shipped source is changed.

The earlier statement that original `Prepared::new` transport was unproved is
superseded at the following explicit child-interpretation scope:

- `CurrentOriginalPreparedNativeV1.eq_prepare` proves TOTAL complete Result
  and scratch equality between the fresh original body and retained preparation.
- `CurrentOriginalPreparedCarrierTransportV1.prepare_transport` proves TOTAL
  equality on the complete fresh current carriers, including Transcript/hash
  state. No opaque Prepared replacement or chosen successful output is used.
- `CurrentOriginalPreparedInstallationV1.first_original_new_claim_and_rank`
  installs that original body in the enclosing first caller. One enclosing
  success derives the decoder, selected View/semantic execution, scratch,
  canonical gamma/kappa, original-payload claim meaning and joint rank trace.
  The original nested claim implementation and RustStd/powers/serializer
  installation are still separate obligations. S1 is not closed by this join.

S2 now has passing checks on actual SDK code, not only the old observer model:

| Concrete target | Attempt | Exit | Wall s | RSS KiB | Swap |
| --- | --- | ---: | ---: | ---: | ---: |
| Metadata guards, accept/borrow/metadata covers | sdk-metadata-guards-v5b | 0 | 2.655 | 121556 | 0 |
| Distinct keys, duplicate/distinct covers | sdk-distinct-guards-v5 | 0 | 4.161 | 326984 | 0 |
| Complete stage1 prefix through exclusive checkpoint acquisition | sdk-stage1-prefix-guards-v1 | 0 | 6.608 | 393148 | 0 |
| Checkpoint iterator next at every cursor 0..1768 | sdk-buffer-next-step-v1 | 0 | 4.971 | 367608 | 0 |
| Actual std any on every 0..16-byte chunk | sdk-buffer-chunk-v1 | 0 | 1.647 | 279708 | 0 |
| Owned checkpoint snapshot with live exclusive guard | sdk-owned-snapshot-v1 | 0 | 9.910 | 382416 | 0 |
| Arbitrary checkpoint copy/writeback, any selected index | sdk-checkpoint-copy-v5 | 0 | 3.761 | 375352 | 0 |
| Verbatim SDK suffix after zero scan; child argument provenance | sdk-stage1-tail-v1 | 0 | 15.490 | 2155952 | 0 |
| Suffix after proof guards; child errors and successful writeback | sdk-stage1-tail-v2 | 0 | 34.428 | 1562572 | 0 |

The first suffix check keeps the real SDK borrows, the full statement and
Public carriers, both statement variants, validation/afterstate-encoding
pointer correspondence, original public-byte pointer/length, exact proof
suffix pointer/length, split index and release `None`. The verifier child
returns Err after the argument assertions. Its reached-call cover passes.
The second suffix check admits successful children and tests checkpoint
writeback, with two earlier proof comparisons explicitly cut at its entry.
Neither is mislabeled as a whole-stage certificate. The output fill pattern
in that root is bounded; the independent arbitrary-byte copy certificate
supplies the general copy operation. SDK alias, failure-domain and entry-cut
conditions remain explicit in the individual source-cut manifests.

Following the owner's continuation instruction, the long zero scan is handled
by a symbolic SDK next step and Lean induction rather than a larger whole-stage
Kani job. `S2OwnedCheckpointScanTotalV1.scan_total` proves the **actual emitted**
owned Vec scan TOTAL for every representable length and all U8 contents,
including checked index/addition totality. It uses a decreasing remaining-byte
measure, not concrete normalization of 1768 iterations. The separate
`S2CheckpointScanCompositionV1` preserves short-circuit suffixes under arbitrary
chunk composition. Kani's Rust compiler version and upstream slice iterator
source are pinned in `modular-host/std/`; the symbolic SDK step tests the real
compiled iterator and all empty/continue/return cases. The Kani tool boundary
is named P6 evidence, not a Lean axiom.

The owned stage1 continuation extracts successfully. Its complete emitted
body is kernel-checked in `S2OwnedStage1ModelV1`, with full ProgramError,
statement and verifier types. There are no imported external-template axioms.
Its thirteen named Ops fields expose remaining child interpretations:
slice/array inequality, Option.ok_or, actual tx1, proof-length constant,
statement validation, actual decoder, afterstate-size constant, encoder,
digest clone/digest, error/log mapper, ordered public snapshot and ordered
proof snapshot. Public read, decoder/validator/encoder, proof read, child
call and writeback remain in the shipped order. No premature SDK borrow or
snapshot acquisition is silently substituted.

`S2OwnedStage1ReachabilityV1.tail_success` removes separately supplied public
snapshot, decoder-box result, selected statement/Public, proof snapshot,
selected proof slice, split-byte cast, child success/None and checkpoint-copy
premises from this enclosing **owned-reference** theorem. They are derived
from the same success. Exact snapshot/range/index/cast/copy equations are in
the conclusion. This is ACCEPTED-ONLY reachability; the owned scan's TOTAL
result must not be promoted to totality of the complete SDK stage.

**Remaining S2 deliverable:** install the actual decoder and current tx1 in
this emitted reference, then finish the concrete ordered SDK snapshot/borrow
and source-cut composition certificate so the enclosing actual SDK theorem
consumes it. Account-data alias partitions, retained guard lifetimes, rejected
paths, full byte-copy correspondence and observable errors/log effects must
remain covered. The owned model by itself does not discharge those SDK IO
fields. The parser and compact expansion cone is owned by the other live
session; import its landed total/frame certificates rather than reprove it.
No new source-adoption decision is requested for this reference-only route.

All 18 current accepted Lean targets pass the source-only checker; all audits
use subsets of propext/Classical.choice/Quot.sound. Receipts and exact import
pins are authoritative for timings. Failed local drafts, timed-out broad
SDK roots and unsupported generic-trait stubbing preflights are retained and
excluded. The old Kani output format reports satisfied covers as raw FAILURE
properties; the accepted terse-mode rerun explicitly reports all covers
SATISFIED and exit0. No exit1 run is accepted merely by interpreting its log.
No unchanged full Lean replay, production verifier rewrite, SBF rebuild or
security-contract reduction was performed. The 100-bit target is not yet
established.
