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


### Continuation: concrete decoder/current verifier, owned scan and retained children

This addendum supersedes the earlier remaining-deliverable item that still
listed installing the decoder/current tx1. The source freeze is still
`b2727acd3abf79315d18b754a260f58f4b1c6326`. No production source changed.
The landed parser dependency is pinned to research `e5a601bea1d808531dbc296ae120b6886a4a9e68`;
it was imported as source/hash evidence and a checked warm object, not rebuilt.
`reused-parser/pin.json` records the exact source and matching attempt-6 receipt.

`S2OwnedCurrentCarrierV1` supplies reversible complete statement/common,
afterstate/payment and Public maps and constructor-preserving maps for all
seven nested decoder-error enums. Both statement variants and all error
payloads are retained. Naming generated discriminant instances was extended
to all thirteen enums to avoid a collision with the actual decoder import;
discriminant codes and carriers are unchanged.

`S2OwnedSourceInstallationV1.install` now supplies nine of the thirteen
emitted child operations: actual slice/array comparison, actual Option.ok_or,
current compact tx1, proof-size constant, actual retained validator, actual
retained decoder, afterstate-size constant, actual retained afterstate
encoder, and digest clone. These use the source files already pinned by the
S6 retained-source correspondence; the complete decoder/statement source
files match, not merely their public function names. `decoder_validated`
reuses the existing actual decoder success theorem to show it validated
exactly the mapped returned statement. No independent validation premise is
added, and validators/encoders remain in their original execution positions.

Before this installation, `Reachability.tail_success` left the decoder,
validator, encoder and current tx1 as Ops interpretations. After installation,
`tail_current_first` takes one success of the same emitted owned tail and
derives the actual same-byte decoder equation, exact proof range
`688..58295`, original instruction-byte/cast equation, actual current
`firstCurrent` success and exact checkpoint-copy equation. There is no
independent decoder, selected Public, tx1-success or observer premise. The
complete carrier, Result, error constructors and output are retained.
`checked_end_total` and `tag_offset_total` prove the source checked additions.
`S2OwnedDecoderLengthV1.actual_wrong_length` proves TOTAL actual WrongLength
rejection for every other representable slice length; accepted decoding's
1880-byte width is reused from `DecoderSuccess.decode_success`.

`S2OwnedSnapshotTransportV1` imports the landed parser's `to_vec_bytes`, which
is TOTAL for all representable lengths. Its complete Result transport and
enclosing tail equality preserve errors, failure and divergence. This
replaces the abandoned whole-58295-byte SDK copy check, which was stopped
at about 6.1 GiB rather than rerun unchanged with a higher cap. It does not
itself instantiate the ordered live SDK borrow operations.

`S2CheckpointGuardTransportV1.owned_eq_std` combines the emitted loop's
TOTAL theorem with the pinned std-any sequence model. `guard_eq` transports
an arbitrary complete result/state/trace carrier through that exact guard.
`S2OwnedGuardCompositionV1.guarded_current_first` composes this concrete owned
scan and the installed tail: one guarded success derives all-zero input,
actual decoder and actual same-byte current first execution. Its
`nonzero_reject` also preserves the precise AccountAlreadyInitialized result
and unchanged checkpoint on rejection. These are reference composition
results. The actual SDK iterator representation and wrapper coupling must
still be supplied; a sequence model is not asserted to be that instance.

The strengthened actual SDK iterator step additionally preserves an arbitrary
selected checkpoint byte. Its `sdk-buffer-next-frame-v2` certificate passed
in 5.479 s, 367088 KiB RSS, swap0, with all cursor/end/continue/return cases.
The actual SDK public owned-snapshot check passed in 13.755 s, 380356 KiB,
swap0, with live shared aliases, exclusive rejection and guard release.
Exact commands, source/tool/import hashes, exits, timings, RSS, swap and
axioms audits are in the individual receipts; all current accepted Lean
audits use only subsets of propext/Classical.choice/Quot.sound.

**SDK diagnostic limits, not closures.** A direct GOTO parent check with only
the pure std-any result abstracted reports 1159 ordinary assertions passing
and one attainable reached-child cover in 20.511 s, 2307504 KiB, swap0.
Raw CBMC exit10 is retained, and every property/status is exported without
its large counterexample trace; the full raw log is hashed and retained on
the host. No exit10 is mislabeled as cargo-kani exit0. This confirms a viable
parent context under a named cut, not a concrete source equivalence result.
The expanded all-alias/success parent timed out at 181.084 s, 6410252 KiB;
the split alias diagnostic first exposed an insufficient memcmp unwind and
then timed out after its bound was corrected. Those runs are excluded.
The independent successful-parent diagnostic was stopped after resource
review at 148.975 s, 6390320 KiB. All used fresh admission, explicit 6/8 GiB
limits and MemorySwapMax=0. No unchanged larger rerun is planned: finish
with verified blocks/steps and composition.

**Exact outstanding scope:** the four remaining owned caller fields are the
Solana digest operation, exact verifier error/log mapper, ordered SDK public
read/snapshot and ordered SDK proof read/snapshot. Current verifier Ops also
remain explicit and retain their separately owned source/security obligations.
The missing S2 source theorem must concretely couple the frozen AccountInfo
stage1 to this reference, including complete SDK alias/borrow semantics,
retained guards, byte snapshots, errors, writeback and observable traces.
S6's enclosing same-statement reuse is proved in the installed reference,
but actual SDK execution still shares this S2 gap. S1 retains original nested
prepared_claim and original from_fn/gamma-power source correspondence and
its actual primitive/standard-library obligations. No S1/S2/S6 whole-cone
closure or 100-bit release is claimed: **target not yet established**.
All work is in the isolated branch. No new production/source-adoption decision
is requested for these reference-only changes. Candidate adoption would still
require complete source equivalence and a fresh release/artifact pin.


The replacement SDK alias leaves now pass independently:
`sdk-shared-alias-step-v1` (exit0, 12.682 s, 1333772 KiB RSS, swap0,
0/483 failed, 2/2 covers) checks identical shared slice pointer/length/selected
byte across every length0..58295 and all storage bytes. Thus one shared view
cannot satisfy both accepted public/proof lengths. `sdk-exclusive-alias-step-v1`
(exit0, 2.974 s, 366284 KiB, swap0) checks exact AccountBorrowFailed under the
live exclusive guard and successful re-borrow after release. These are real
SDK alias steps, not acceptance of the excluded whole-parent diagnostics.
The generic SDK/runtime arbitrary-capacity RefCell counter boundary and the
complete enclosing source composition are still required.

The packet checker now rejects stale own direct-import hashes as well as
stale source/object receipts. This found the carrier proof pre-dating the
latest reachability object; that proof and its affected installation/guard/
decoder-length dependents were recompiled, without replaying unchanged
unrelated targets. The exact current closure is pinned after those checks.
The debug-format error/log leaf was also probed, then stopped when both a
symbolic enum root and a constant-Parse preflight retained about6.1GiB
without a result. Neither is accepted; exact error/log interpretation is
still in the remaining-field list. No resource cap was increased.

Before this checkpoint, the main research worktree was inspected read-only at
`b5b7c5ce32a5a7896db53ecc1d4ca98d1258532e`. Its current S6 re-pin and S1
handoff still explicitly name frozen `b2727acd3`; the overnight handoff keeps
the next-freeze candidate parked. No new freeze is inferred from intervening
S3/S9 source-proof commits. This branch/worktree remains isolated.


### Full owned SDK reference continuation (2026-10-21)

S2 remains OPEN. The full `owned-sdk-v3` reference retains account metadata,
separate data/lamports alias slots, signed borrow counters, strong/weak counts,
all bytes, guard acquisition, ordinary-return releases, and checkpoint writes.
This is an isolated reference, not an adopted production change. The shipped
SDK-to-reference heap/trace correspondence is not inferred from extraction.

The reference extracted successfully after replacing unsupported extracted
signed AddChecked/SubChecked expressions with signed checked_add/checked_sub
and unwrap. The exact isize carrier is retained. `owned-sdk-v1` is a retained
failed extraction; v2 and v3 are successful. v3 includes the actual checkpoint
size/Variant helpers. Its full emitted Types and Funs compile as
`S2SdkOwnedTypesV1` and `S2SdkOwnedModelV1`; installation also compiles and
installs ten of twelve helper fields, including the actual decoder, validator,
encoder, compact tx1, sizes, equality operations and clone. Remaining fields
are digest and error/log interpretation, alongside the imported current
verifier's own child contracts. This is not closure of those contracts.

Focused actual-SDK joins now compare the exact owned reference shared acquire,
exclusive acquire and temporary length read against the pinned SDK for every
signed counter, all metadata and all byte values in the explicit 1768-byte
domain. Accepted receipts are sdk-owned-shared-join-v2 (9.251 s,
425584 KiB), sdk-owned-exclusive-join-v1 (8.951 s,425928 KiB), and
sdk-owned-length-join-v1 (6.961 s,423456 KiB); each exits zero with swap zero.
The predecessor shared join v1 failed its harness unwind bound and is excluded.
The counter-injection harness validates the pinned RefCell layout with real
SDK acquire/drop operations first; this is compiler/layout-specific evidence,
not a portable-layout theorem or an arbitrary-account-length proof.

`S2FrameOperationsTotalV1` proves guarded emitted range, prefix, compact suffix,
tag read and copy operations total. `S2OwnedFrameReachabilityV1` derives the
proof and checkpoint length guards from successful execution of the earlier
owned tail. These guarded operation and accepted-only reachability results
are distinct. The complete SDK-parent accepted-only reachability proof is
still being developed; failed attempts are retained and excluded. Its tactic
splits outer conditions without normalizing full parser/arithmetic bodies or
raising Lean resource options.

Remaining enclosing S2 obligations are the successful full-reference parent
connection, concrete shipped SDK-to-reference construction/composition with
all aliases/errors/state/trace effects, relevant totality and wider byte/frame
contracts, then the composed premise audit and coherent pinned validation.
S1 and S6 are not declared closed by this continuation.


The complete reference-parent connection is now checked as
`SdkReference.Reachability.stage1_current_call` in
`S2SdkOwnedReachabilityV1.lean`, receipt
`s2-sdk-owned-reachability-v17`: exit0,14.551363s,
3297067008 bytes peak RSS,swap0,Lean -j1 -M4400. Its only execution
premise is `owned_stage1 (Installation.install ops verifierOps) program sdk
 data = ok (.Ok (),sdkOut)`. Its conclusion derives an actual current compact
`tx1 verifierOps` success at the same explicit SolanaDigest installation,
Unit state and observer None. It assumes no independent decoder, child-call,
borrow-result or callback-success premise. The theorem is ACCEPTED-ONLY and
concerns the complete owned reference; the SDK-source construction relation
and its transport are still not proved. Digest/error interpretation and the
current verifier child dictionary retain their existing boundaries. The
existential call arguments are derived from the source execution, but this
statement does not yet expose their decode/semantic projection witness.

The proof traverses only emitted parent binds/conditions and branch equations;
callee implementations are not normalized. Empty Infallible residual branches
are eliminated explicitly. The successful theorem depends only on propext,
Classical.choice and Quot.sound. Failed trials (including generated sorryAx
from failed elaboration) are excluded and must not be cited as proof evidence.
`S2SdkOwnedScanTotalV1` is also checked: it transfers the existing TOTAL scan
through exact emitted function identity and proves release with no guards is
identity. This is not release-totality for arbitrary supplied guard records.
The packet consistency check accepts31 current focused targets; it regenerates
both old-tail and full SDK reference adapters from the pinned emitted text.
