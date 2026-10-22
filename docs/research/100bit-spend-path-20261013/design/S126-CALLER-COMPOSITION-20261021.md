# S1 / S2 / S6 current compact caller composition — 2026-10-21

**Target not yet established. S1, S2 and S6 are not closed as actual SDK-to-release cones.**
This is an additive proof/source-cut packet, not a production verifier change.

## Freeze and scope

- Historical extraction source: `b2727acd3abf79315d18b754a260f58f4b1c6326`.
- Current adopted source overlay: `25866ec331cc7ce27dd9956609c11d32fa8fa58a`, containing
  user-authorized S4 adoption `29cbab431742f7e899870595167efa193a379f0a`; C3-BIN
  2026-10-22 11:50–12:40 addenda supersede old ELF/source authority. Four caller
  files are byte-identical, recorded in `caller-source-adoption-overlay-20261022.json`.
  This identity overlay does not reassign historical transitive S4/powers proofs.
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


`S2SdkOwnedDecodedReuseV1.stage1_decoded_first` now strengthens the complete
owned-parent conclusion to expose one matching boxed decode, the semantic
projection of that exact object, and first_decoded on that exact public slice.
All three equations are derived from the single enclosing owned_stage1 success;
none is an added premise. Constructor equations from Try::branch are explicitly
propagated, rather than treating its Continue payload as independent data.

`stage1_current_first` consumes that witness and the existing actual-decoder
and S6 decoder-scoped reuse transport. From the same single parent execution
it derives actual decodeActual success and firstCurrent success on exactly the
same public bytes. `semantic_public_eq` checks the full newly emitted semantic
projection equals the earlier checked projection by definitional equality.
The current successful receipt is s2-sdk-owned-decoded-reuse-v4: exit0,
28.996379s,3117383680 bytes RSS,swap0,-j1 -M4400; all three axioms audits
contain only propext,Classical.choice,Quot.sound. v1/v3 failures are excluded.
This removes the old independent decode/public/caller premises at the complete
owned parent boundary. It does not yet establish the corresponding instance
for the shipped SDK parent, nor identify the slice with an initial SDK account
buffer through a proved heap-construction relation. No whole S2/S6 closure or
100-bit release conclusion follows at this checkpoint.


### Same-byte parent, SDK write sets and guard arithmetic continuation

The latest decoded-reuse receipt is now s2-sdk-owned-decoded-reuse-v6:
exit0,7.620981s,3451830272 bytes RSS,swap0. In addition to the three-call
witness and current first composition, `stage1_current_first_split` derives
split10 from that same parent success through the already checked compact
source guard. The outer release admits [3,11], but the existing
CurrentCompactReleaseRejectV1 theorem rejects11 at compact tx1; no adversary
input restriction is introduced. This matches the fixed split in dV_frozen2.

`S2SdkOwnedPrimitivesTotalV1.bytes_clone_total` proves the exact emitted Vec
byte-clone is TOTAL identity for arbitrary typed byte vectors, by the existing
library clone induction. `shared_allowed_exact/true` cover the entire signed
counter domain. Current receipt primitives-total-v3: exit0,15.507505s,
2236481536 bytes RSS,swap0,standard-only audits.

`S2SdkOwnedBorrowTotalV1` now proves exact valid-slot read/update operations,
temporary length read, checkpoint acquisition and shared acquisition, including
their ordinary AccountBorrowFailed results and full returned SDK state. Shared
increment and positive-count decrement are TOTAL signed checked operations.
Current receipt borrow-total-v8: exit0,4.366439s,2263498752 bytes RSS,swap0,
standard-only audits. Slot validity is an explicit domain obligation here; it
must be derived by the actual enclosing SDK construction/caller, not assumed
closed by these local results.

`S2SdkOwnedGuardReleaseV1.release_total` composes the complete emitted reverse
release order under its explicit LiveInvariant. That invariant tracks valid
slots, exclusive count-1 and exclusion from both shared slots, plus enough
shared count for each live guard, including public/proof aliasing. Literal
release subterm identity is checked by release_eq. Current receipt
guard-release-v5: exit0,11.010643s,2278637568 bytes RSS,swap0,standard-only
audits. This is conditional TOTAL; the parent-body acquisition invariant
instance remains to be derived. It is not a replacement assumption that
closes S2.

The direct selected-byte wide Kani query sdk-owned-descriptor-frame-v2 did
not complete: it was stopped at the ten-minute review (9:59); the runner
recorded exit1,602.044s,3476408KiB RSS,swap0. It is excluded. The descriptor/
counter predecessor sdk-owned-descriptor-join-v1 passed in5.129s,
428220KiB,swap0,over all view lengths0..58295. No larger cap retry was used.

The replacement checks an actual memory write-set contract on native SDK
acquire/drop rather than selecting a byte in the large buffer. The two v2
harnesses retain real AccountInfo/Rc/RefCell and the exact original
try_borrow_data / try_borrow_mut_data and guard drop operations. They permit
only the actual signed borrow counter cell to be assigned and require its
original value on return. Thus the checked operation cannot assign to account
buffer memory, SDK slice descriptors, keys, flags, rent_epoch, lamport values,
or Rc headers. Input buffers contain all58295 symbolic bytes with view length
0..58295; signed borrow counts range over all isize values. Both data and
lamport Rc strong/internal weak counts range1..isizeMAX; the private compiler
layout is validated against public SDK operations/count accessors before
logical-count injection. Lamport borrow counters start at the SDK constructor's
zero; no arbitrary lamport-borrow counter domain is claimed.

- sdk-shared-write-frame-v2: exit0,35.368s,4653828KiB RSS,swap0,
  0/761 failed assertions,2/2 covers.
- sdk-exclusive-write-frame-v2: exit0,27.639s,4754044KiB RSS,swap0,
  0/795 failed assertions,2/2 covers.

Fresh admissions,6GiB/8GiB cgroups and MemorySwapMax=0 are recorded. The
property audit inspects the already checked GOTO without another solver run;
it confirms actual SDK/stdlib assigns checks and the counter-restoration
postcondition. Only source, text metadata and binary hashes are distributed.
Kani0.67.0 function-contract and compiler/layout trust boundaries are explicit.
The actual Cargo fingerprints confirm -C opt-level=3,overflow-checks=yes and
the Kani compiler/sysroot flags despite Cargo's generic dev-profile label;
Kani library hashes and contract source pins are retained. The dedicated
check-sdk-frame-packet.py validates sources, dependency versions, receipts,
flags, assignment/postcondition metadata and resource limits; the general
packet checker invokes it.

The actual checkpoint-size helper is also TOTAL1768: the new
S2SdkCheckpointSizeTotalV1 proves literal emitted helper identities to the
already checked R22 CHECKPOINT_FIXED and Tx1FinalLenBoundV8 functions, then
reuses their symbolic proofs and two small checked arithmetic operations.
No unchanged arithmetic dependency is rebuilt. Receipt checkpoint-size-total-v2:
exit0,14.343054s,2255339520 bytes RSS,swap0,standard-only audits. The missing
R22ControlBounds cache in the initial attempt was found and reused.

Before these pins, research was re-inspected read-only at
67851f0ab48d40e8df404efc18d65326238804d5. Its S2/S6 re-pins still name
b2727acd3, and both SDK program files have no diff against that freeze.
The current handoff's integration endpoint is
OraclePortHeadlineFrozen2PerAttempt.final_soundness / dV_frozen2, under the
unchanged raw per-attempt SECURITY-CONTRACT-20261021.md. This continuation
makes no numerical completion claim and changes no frozen production source.

Remaining: instantiate the live-guard invariant from the complete owned parent
on every ordinary return; complete the concrete shipped SDK account/snapshot/
alias construction and ordered parent-step correspondence (including errors,
writeback and release effects); feed that instance into the adopted two-tx
ordered-log/source join. The checked parent decode/first/split conclusions and
native operation write frames remove specific local premises, but no whole
S2 or S6 closure is claimed. S1 still needs its original nested claim/powers
and preparation trace premises discharged through this caller connection.


## Complete owned-parent guard finalization, 2026-10-21 continuation

S2SdkOwnedGuardAcquireV1.checkpoint_acquire_invariant and
shared_acquire_invariant now derive their postconditions from each actual
emitted acquisition return. Slot validity follows from the reached Vec.index;
no independent slot-validity or acquisition-success premise is introduced.
Shared aliases, signed counter bounds and ordinary error statuses are retained.
S2SdkOwnedGuardFrameV1.write_bytes_invariant uses the exact reached mutable
index/setter and proves that the checkpoint bytes assignment preserves the
live-guard invariant.

The enclosing S2SdkOwnedGuardBodyV1.body_live_invariant starts from the actual
empty guard record and the single complete owned_stage1_body execution. It
establishes LiveInvariant on every ordinary return, both Ok and Err, with
arbitrary child Ops. No separate guard invariant, slot validity, child success
or write-frame premise remains in this theorem. The companion
body_return_finalizes composes that result with release_total: any ordinary
body return produces a complete owned_stage1 return with exactly the same SDK
status. The previous separate live-invariant and release-success assumptions
are discharged at this concrete reference parent. This is conditional on the
body returning; it is not TOTAL termination for arbitrary external operations,
and is stronger in status coverage than an ACCEPTED-ONLY statement.

Focused receipts: guard-acquire-v5 exit0,10.335s,2261991424 bytes RSS;
guard-frame-v2 exit0,13.522s,2247540736 bytes RSS;
guard-body-v13 exit0,11.391458s,3233398784 bytes RSS. All swap0, one local
mkdir lock, -j1 -M4400, standard propext/Classical.choice/Quot.sound only.
The failed body attempts are excluded. The replacement proof reduces one
outer bind/branch/tuple-pattern helper at a time, retaining arbitrary child
implementations. Exact Expr assertions avoid repeatedly re-elaborating the
same guard facts; only guard records use default definitional transparency.
No resource-option override or unchanged full replay was used.

Before this checkpoint, research was read-only rechecked at
496879d8fb01640c9cf091f5e797069bc98fe035; the two frozen SDK program files
still have no source diff against b2727acd3. The reference remains an isolated
proof candidate, with no production adoption or re-pin implied.

S2 remains OPEN: the shipped SDK account/snapshot/alias construction and
ordered parent-step correspondence must still connect to this complete owned
reference, including native errors, writeback and guard drops. The concrete
Std iterator/copy bindings and the adopted dV_frozen2 ordered-log join remain
explicit obligations. Native step certificates plus this parent theorem do
not by themselves instantiate that join. S6 and S1 retain the previously
recorded source/caller obligations; the 100-bit target is not yet established.


## Actual std-any body and complete SDK-reference scan installation

This continuation replaces the previously hand-written std-any sequence-body
boundary with an extraction of the actual reached Rust std method. The warm
full-MIR Charon sysroot was essential: distributed-sysroot extraction had
already inlined next into raw pointer/global operations despite --mir built.
The full-MIR extraction std-any-v5 (Charon exit0,.255s,143792KiB; Aeneas
exit0,.368s,69344KiB; both swap0) emits the real any body, loop, predicate,
trait implementations and caller. The exact method text is byte-identical
between the pinned Kani compiler's upstream std source and the Aeneas std
source, checked in std-any-source/source-pins.json. This is method identity,
not a claim that the two compiler/sysroot binaries are identical.

The emission adapter retains both native Iter pointer fields and its Unit
marker, all callback state, short circuit and returned iterator. The otherwise
uninterpreted NonNull/ConstRawPtr carriers and reached next/constructor are
explicit parameters, never custom axioms or an asserted native implementation.
S2StdAnySourceTotalV1 checks the loop induction and contextual guard transport.
The next contract explicitly requires the constructor-established valid
iterator domain and preserves it; it does not demand sensible results from
arbitrary malformed pointer pairs. This correction adds no restriction on
verifier inputs: validity is derived by the concrete constructor below.

The missing instance is now supplied at the full owned SDK-reference level:
S2SdkSourceIteratorV1 retains all four exact SDK rows (accounts, complete data
and lamport heaps, counters and Rc metadata), plus the concrete slot/offset
pointer fields and the complete emitted source_begin/source_next functions.
S2SdkSourceIteratorTotalV1.next_reads proves every assertion, selected-cell/
byte index and checked cursor increment total from the constructed invariant;
begin_total establishes that invariant and the byte view. No native-next,
constructor-success or cursor-range premise remains in its enclosing guard.
The logical pointer identity is a data-heap slot plus offset. Its native
physical-pointer correspondence is a separately checked operation boundary,
not inferred from this representation or from equal booleans.

That boundary is checked by sdk-iterator-reference-join-v3: the actual SDK
AccountInfo RefMut remains live, with every1768-byte value and cursor0..1768.
Both the actual iterator constructor and one actual next call are compared
to the exact owned functions later extracted by Aeneas. Result byte, physical
next pointer, remaining length, logical object identity/end and lamport value
agree. Kani exit0,6.094s,420412KiB RSS,swap0;0/1053 failed and3/3 covers.
The native and extracted constructor/next bodies are identical even though
v3 adds constructor harness assertions; no unchanged extraction was replayed.
Native Rc counts in this fixture start at constructor values; reuse the
separately checked all-signed-counter/all-valid-Rc write-frame certificates
and native next byte-frame certificate for those independent boundaries.
The three-account alias/heap construction is still an enclosing obligation.

S2SdkSourceScanV1.snapshotScan_eq_sourceScan now proves all-outcome equality
of the complete emitted read/clone/owned-scan block and the actual std-any
body with those concrete SDK constructor/next functions installed, including
invalid slots. There are no scan, iterator, copy-success, all-zero, byte-value
or native-step semantic premises in this reference theorem. This is equality
in the checked Aeneas Result/library semantics; allocation abort/runtime and
compiler/SDK interpretation remain the named P2/P6 boundaries.

Crucially this is lifted through the complete parent, not left as a leaf:
S2SdkNativeScanParentV1.body_factor checks the exact fission of both scan sites
in the whole emitted owned_stage1_body. body_eq_source installs sourceScan
for both admitted instruction branches. stage1_eq preserves the complete
status and every SDK field, including failure/divergence in the denotation.
body_return_finalizes derives safe release for every ordinary returned body
status. stage1_current_first_split derives actual same-byte decoder/first
execution with fixed compact split10 and release None from a single complete
source-scan-parent accepted execution. It retains the existing concrete child
Ops/digest/runtime boundaries; it adds no child-success or scanner premise.

Focused local receipts (one mkdir lock, -j1 -M4400):
- s2-std-any-source-v2: exit0, 3.007280s, 2255519744 bytes RSS, swap0.
- s2-std-any-source-total-v7: exit0, 5.150989s, 2260893696 bytes RSS, swap0.
- s2-sdk-source-iterator-v1: exit0, 11.417362s, 2243936256 bytes RSS, swap0.
- s2-sdk-source-iterator-total-v2: exit0, 4.603860s, 2257747968 bytes RSS, swap0.
- s2-sdk-source-scan-v1: exit0, 4.126406s, 2245017600 bytes RSS, swap0.
- s2-sdk-native-scan-parent-v5: exit0, 17.208499s, 3271688192 bytes RSS, swap0.
All successful audits use only propext/Classical.choice/Quot.sound. Failed
elaborations/extractions are excluded. check-sdk-iterator-packet.py validates
native command/source/optimized flags/resource limits, exact native/extracted
body identity, both emission adapters and complete parent regeneration. The
normal packet check invokes it. No unchanged full manifest replay was run.

Research was rechecked read-only at d9865ba52cfe0dc617f4ff97a3677b1e330e9b87;
the two frozen program files still have no source diff against b2727acd3.
No production source or other cone was changed, and no adoption/re-pin is
implied by the isolated reference/verification sources.

S2 remains OPEN. The std-any control-flow and concrete SDK-reference scan
installation obligations above are closed at their stated source/leaf scope.
What remains is the actual AccountInfo heap/alias/snapshot construction and
ordered correspondence of the enclosing shipped stage1 steps, including
error/drop/writeback timing, followed by the current dV_frozen2 source/log
join. Concrete syscall/library/runtime boundaries must be kept distinct from
that missing refinement. S6 retains the shared shipped-caller gap. S1 retains
its original nested claim/powers/preparation-trace premises. No whole S1/S2/S6
or global 100-bit conclusion is asserted: target not yet established.

## Addendum 2026-10-21 21:48 UTC — native metadata and decoder-entry cuts

S2 remains OPEN. This addendum closes the following scoped SDK obligations;
it does not close `AcceptedRunJoin D rust` or promote a source cut to a whole
SDK execution. The authoritative protocol freeze is still b2727acd3abf79315d18b754a260f58f4b1c6326.
Research was inspected read-only at 57ca9c4525f0006b40b692bda88bcb99fab71d7d;
the frozen program lib.rs and r1_pool_adapter.rs remain unchanged there.

`sdk-parent-cuts/accepted-cuts.json` selects the exact checked source/tool/
command/resource receipts. `check-sdk-parent-cuts-packet.py` regenerates every
selected Rust candidate and both full-parent Lean fissions, checks SDK lock
versions, optimized compiler flags, properties, native source cuts and pins.
The normal packet check invokes it. No unchanged full replay was run.

* The three-account native heap checks now retain independent data and lamport
  alias maps, all account metadata, every signed borrow counter, full symbolic
  buffers and lengths 0..10485760. Shared acquire/drop, exclusive acquire/drop
  and data length agree with the complete owned SDK state. Native Rc headers
  in these fixtures are those of the constructed graph; arbitrary safe header
  counts are checked separately by the broader write-set contracts, not
  silently attributed to these fixtures.
* The lifecycle cut retains all three real Rust guards in source order and
  checks native/reference counter traces at each reached acquisition and on
  every cut return. It covers returns after checkpoint, public and proof
  guards, including success. Children are explicit return-phase cuts; this
  is not a check of parsing, hashing or the complete stage1.
* The shared/exclusive write-set contracts now cover 10 MiB buffers, every
  signed data and lamport counter and all safe data/lamport Rc header counts.
  Their assigns/postcondition audits confirm that only the selected borrow
  counter is written and its old value is restored. The v2 certificates are
  retained unchanged as historical narrower evidence.
* `S2SdkAliasPartitionV1.independent_heaps` proves every three-handle identity
  pattern has an exact three-slot representation in each heap independently.
  Distinct keys are not assumed to imply distinct data identities. Runtime
  construction of the full heap embedding remains an enclosing boundary.

`sdk-metadata-prefix-join-v2` checks the exact frozen stage1 prefix through
`require_verifier_checkpoint`, before persistent guards. It compares every
ordinary native/reference status, including duplicate keys, malformed
instructions, metadata rejection and the SDK size-borrow failure; all heap
counters remain unchanged. It preserves the exact native helper bodies and
the exact owned prefix, with no scanner/decoder/parser/oracle stub. Domain:
three real AccountInfo values and the complete heap domain above. The enclosing
reference connection is `S2SdkMetadataParentV1.body_factor` / `stage1_eq`:
the kernel checks both original complete continuations and final cleanup,
all outcomes, without a metadata-success or release-success premise. This is
fission of the original parent, not a replacement metadata carrier.

The next native cut is `sdk-prefix-context-check-v3`. The complete frozen
stage1 body is retained. Its decoder cut retains the real 1880-byte rejection,
then checks the exact admitted public root pointer and once-only entry before
returning InvalidAccountData. Every signed data/lamport counter is restored
on every returned prefix status. Root storage remains arbitrary58295/1880/1768
bytes with arbitrary metadata/alias maps. The native std-any body alone is
overapproximated by a nondeterministic bool; its exact scan/byte-view instance
must still be composed from the previously checked std/SDK iterator packet.
All 3611 non-cover properties are SUCCESS; the single cover is reachable.
Raw CBMC exit10 is retained: its sole failing assertion is the cover, whose
counterexample witnesses reachability. The checker does not relabel other
assertion failures or accept an empty property set. This is a decoder-entry
cut, not an accepted whole-stage refinement or unrestricted-length theorem.

The v2 decoder cut was false: stage1 can pass an incorrectly sized public
buffer to the decoder, which rejects it. The failed harness incorrectly
asserted the length before that rejection. Its source, counterexample property
projection and receipt are retained and excluded; v3 preserves the actual
length rejection. Earlier whole paired/native contexts timed out in generic
instrumentation and are excluded. The raw runner was corrected to establish
the Kani harness entry and retain the normal library/undefined-body/backedge
pipeline, with commands witnessed by a separate tiny semantic preflight.
No safety or unwinding checks were disabled. The general ProgramError equality
metadata attempt was stopped at about 6.1 GiB RSS and replaced with the exact
five-status relation; that replacement passed with about 1.14 GiB RSS.

For concrete snapshot instrumentation, `owned-sdk-snapshots-v1` adds only two
named helpers executing the identical Vec clone. Charon/Aeneas retain all
thirty literal-equal SDK/protocol types and the same twelve Ops fields.
`S2SdkSnapshotEquivalenceV1.body_eq` / `stage1_eq` prove complete old/new parent
equality, all statuses and every SDK field. Their proof term is kernel-checked
Eq.refl after full transparency on symbolic bodies; no resource override or
custom axiom is used. The source remains an isolated reference candidate;
no production source adoption or re-pin is implied.

Selected native receipts, all swap0, MemoryHigh6G/MemoryMax8G/MemorySwapMax0:

| Target | Exit | Wall s | Peak RSS KiB | Properties / covers |
| --- | ---: | ---: | ---: | --- |
| sdk-heap-shared-join-v2 | 0 | 23.058 | 812212 | 1814 / 5 |
| sdk-heap-exclusive-join-v2 | 0 | 22.435 | 832360 | 1821 / 5 |
| sdk-heap-length-join-v2 | 0 | 22.018 | 841820 | 1742 / 5 |
| sdk-heap-chain-join-v2 | 0 | 124.586 | 3911540 | 2224 / 9 |
| sdk-shared-write-frame-v3 | 0 | 33.226 | 4753852 | 771 / 2 |
| sdk-exclusive-write-frame-v3 | 0 | 28.393 | 4754732 | 805 / 2 |
| sdk-metadata-prefix-join-v2 | 0 | 34.932 | 1191572 | 2038 / 10 |
| sdk-prefix-context-check-v3 | 10 (cover) | 14.746 | 591016 | 3611 success / 1 reached |

Focused Lean receipts (one atomic local lock, -j1 -M4400, all exit0/swap0):
alias-partition-v3 2.254336s/1392640000 bytes; snapshot-reference-v1
8.453849s/2281340928 bytes; snapshot-equivalence-v4 12.129992s/2271543296
bytes; metadata-parent-v2 15.869365s/2226028544 bytes. All accepted printed
axioms are subsets of propext/Classical.choice/Quot.sound. Raw templates and
failed elaborations are excluded from proof claims. Exact tool/source/direct
and selected transitive import hashes are in the source-only packet.

The remaining enclosing premises are unchanged in scope: actual native SDK
embedding and source-step composition through successful decoding, validation,
candidate encoding, proof framing, first_decoded/tx1 and writeback; concrete
child/digest/error-log interpretations; and ordered source/oracle-log transport
into the headline AcceptedRunJoin. The completed prefix cuts provide concrete
pieces of that instance, but the timed-out parent contexts supply none.
S6 retains this shared actual-caller gap despite the complete owned-reference
same-byte/same-decoded-object theorem. S1 still needs original nested claim,
powers/preparation-trace and caller composition. No source adoption decision
has been requested; no production or other-session track changed. The raw
per-attempt 2^-100 target without grinding credit is not yet established.

## Addendum 2026-10-21 22:37 UTC — actual SDK tx1-entry arguments

`sdk-call-prefix-check-v1` now checks the complete frozen native SDK caller
through entry to tx1, using the real AccountInfo/Rc/RefCell types, both full
statement variants and the actual common/semantic_public methods. There is
no reduced statement/error/observer carrier. All 2022 non-cover properties
are SUCCESS; both covers are reachable, including Withdrawal. Raw CBMC exit10
is retained for the cover witnesses. Wall118.170s, peak4435968KiB, swap0;
MemoryHigh6G/MemoryMax8G/MemorySwapMax0. The large raw trace is retained on
the host with SHA/size pins; the packet contains the complete trace-free
property/status projection, not hundreds of megabytes of array assignments.

Assertions establish that validation receives the returned decoded Box,
encoding receives its candidate-afterstate field, and tx1 receives the exact
semantic references from that object, the original public-buffer pointer and
1880-byte length, proof pointer+688 and57607-byte length, the instruction's
split and observer None. Counters are restored on every returned context
path. Decoder length rejection is preserved. No separate supplied pointer,
semantic-object, slice-length or observer agreement is assumed in this cut.

The cut is explicit: decoder/validator/encoder replies are full typed common
successful results; tx1 checks its arguments and returns Ok(empty Vec), forcing
the following checkpoint-length guard to reject before writeback. The error
mapper has an assert-false reachability stub, and that assertion is proved
unreachable for this successful verifier reply. No rejected-child logging
semantics or successful whole-parent equivalence is inferred. Actual child
interpretations and execution-prefix transport to other returned replies must
still be installed. All statement value fields are generated individually
from frozen Rust declarations, including arbitrary u32 M31 storage words;
both variants and noncanonical values are included. Padding is not a value
field. The previous transmute-based factory is retained only in old attempts.

Domain correction: this tx1-entry harness's proof prefix is initialized to
the arbitrary688-byte candidate reply and byte696 is tag2. These are the
admitted source prefix/tag equations, not every joint proof/candidate/tag
combination. Public/checkpoint root contents remain arbitrary. Mismatching
prefix/tag rejection paths are outside this cut; their source/guard composition
remains required. Earlier draft wording about all joint root byte values was
too broad; its qualification was corrected without changing the checked Rust
source or replaying the solver. The packet checker regenerates both the source
and the corrected qualification.

For the post-child block, wide and normalized whole-heap byte-query attempts
and whole-copy dynamic write-set contracts were stopped and excluded, without
raising any cap. Their source, commands, stop reasons, wall/RSS/swap receipts
and admissions remain in the packet. The normalized candidate explicitly
requires the reached58295/1880/1768 wire layout; deriving that entry relation
is still part of the enclosing source transport. It is not an adversary
restriction or a proved whole-source theorem.

The replacement `sdk-finish-step-join-v3` proves one SDK indexed byte assignment
through an actual RefMut with a ghost raw-byte pointer equal to its base plus
the symbolic offset. Its modifies set is exactly that u8 pointer. All611
properties and2/2 boundary covers pass: exit0,8.642s,383508KiB,swap0,6G/8G/0.
It proves the byte equals the old source byte and no write outside that byte
is allowed. The operation is a byte-assignment reference candidate, not the
frozen whole-copy implementation. Count induction and whole-copy equivalence
remain necessary before this can replace the native post-child premise.
The follow-up property audit is read-only: exit0,.222s,42388KiB,swap0,1G/2G/0;
762 static properties,18 selected assign/postcondition properties, exact
source/proof/program/tool pins. No solver replay was performed for that audit.

Fresh admission had one vanished-cgroup race before a paired codegen job
launched. The private admission script now retries the entire snapshot, never
skips the unknown row, and rejects missing roots or unbounded populated
scopes. The paired codegen preflight passed afterwards; it is not a proof and
no paired whole-parent solver was launched from that preflight.

The source-only checker now selects ten cuts at their stated scopes. The
complete SDK/first/decoder Lean targets and their standard-axiom audits are
reused unchanged. S2, S6 and S1 remain OPEN: actual SDK embedding and source
prefix/child/reply/whole-copy/oracle-log composition are not yet a concrete
AcceptedRunJoin instance. In particular, proved tx1-entry arguments do not
alone discharge the enclosing caller premise. No frozen production source,
security metric, protocol parameter, other cone or release artifact changed.

## Addendum 2026-10-22 00:55 BST — full owned copy count and parent equality

The authoritative protocol freeze remains
`b2727acd3abf79315d18b754a260f58f4b1c6326`. Research HEAD
`369becb700710075a4a972604f473f977b81c3ed` was inspected read-only: the
program lib.rs and adapter still have no diff against that freeze. All new
Rust is an isolated reference/harness; no shipped source or release pin is
changed. These candidates require the native/source composition below before
adoption, and any adoption requires explicit equivalence and artifact re-pin.

`owned-sdk-copy-v1` imports the complete existing OwnedSdk, not a replacement
account carrier. Charon and Aeneas extract the actual byte step and while loop
with no new callbacks. Five emitted SDK/error declarations are checked against
the existing full declarations. Exact emitted source, tool hashes, dependency
hashes, LLBC hash/has_errors=false, admissions and receipts are in
`evidence/s126-current-caller-20261021/sdk-parent-cuts`. Charon: exit0,
0.477s,174012KiB; Aeneas: exit0,0.359s,68992KiB. Both swap0, High6G/Max8G/Swap0.

The new checked claims are:

- `CopyLoop.copy_step_total` derives actual reads, setter and byte update from
  valid SDK/source/destination indexes, and preserves the live guard invariant.
- `CopyLoop.copy_loop_total` proves the emitted count loop by decreasing
  source-length minus offset. The invariant retains the entire initial SDK
  and replaces only the selected byte vector. `increment_total` uses the
  actual slice bound to discharge checked usize addition.
- `CopyLoop.copy_in_place_total` covers every valid SDK slot and all source
  contents/lengths, including ordinary length rejection with unchanged state.
  It requires no separate read, setter, increment or loop-success premise.
  This is TOTAL on its stated valid-slot domain, not total arbitrary callbacks.
- `CopyLoop.finish_eq` identifies the loop and original complete final
  assignment on every SDK/slot/source/guard input, including model failure and
  divergence branches. It adds no validity, length or success premise.
- `CopyParent.body_factor` kernel-checks fission of BOTH exact assignment sites
  in the complete original parent. `body_eq_loop` substitutes the proved loop
  equality in that whole parent. `stage1_eq` includes final guard release and
  equality of the complete status/SDK result.

Before/after enclosing statement: the original `owned_stage1_body ops program
sdk data guards` equals `bodyWithFinish originalFinish ...`; it now equals
`bodyWithFinish loopFinish ...` for the SAME universally quantified ops,
program, full SDK, data and guards, with no copy-success, slot or length
hypothesis. Whole `stage1_eq` has the same arbitrary ops and full state and
retains all ordinary errors/cleanup. This removes the copy-loop interpretation
premise inside the owned parent. It does not instantiate actual child ops,
prove their termination, or assert equality to complete native SDK execution.

Smallest changed targets were compiled in dependency order, with the local
atomic lock and `-j1 -M4400`; each exit0,swap0, exact source/tool/direct imports
and axioms recorded in the named focused receipts:

| Target | Accepted receipt | Wall seconds | Peak RSS bytes |
|---|---|---:|---:|
| S2SdkCopyLoopModelV1 | s2-sdk-copy-loop-model-v2 | 3.600339 | 2214002688 |
| S2SdkCopyStepTotalV1 | s2-sdk-copy-step-total-v1 | 4.393219 | 2252701696 |
| S2SdkCopyArrayLawsV1 | s2-sdk-copy-array-laws-v2 | 4.810138 | 2250145792 |
| S2SdkCopyLoopTotalV1 | s2-sdk-copy-loop-total-v5 | 3.367144 | 2262679552 |
| S2SdkCopyAssignmentV1 | s2-sdk-copy-assignment-v4 | 5.289451 | 2254684160 |
| S2SdkCopyParentV1 | s2-sdk-copy-parent-v1 | 7.329930 | 3310419968 |

All printed axioms are subsets of propext, Classical.choice and Quot.sound.
Failed local drafts remain excluded. The packet check now selects55 current
focused targets and11763 selected import objects by hash, without distributing
objects or replaying unchanged Lean proofs. This is not a coherent release
rebuild.

Native whole-copy progress is distinct from the loop proof. The exact frozen
finish block, with its actual RefMut and a borrowed Vec reply, satisfies a
fixed1768-byte write-set contract: `sdk-finish-fixed-frame-join-v3`, exit0,
15.194s,726496KiB,swap0,843 properties and2 covers. Two earlier owned-Vec
versions failed the freeable check and are excluded; no safety check was
disabled. The helper borrows the reply so owner/drop remains with its caller;
transport of that split is still required.

The actual std slice-copy primitive also passes its contract with a real SDK
RefMut destination: `sdk-std-copy-frame-join-v1`, exit0,11.057s,443896KiB,
swap0,525 properties and2 covers. The generic inherent-method bridge, with
that VERIFIED callee, passes `sdk-std-copy-bridge-join-v1`: exit0,3.516s,
208836KiB,swap0,138 properties and1 cover. It checks the reached type is u8,
length1768, and the observed pre-call byte. Its writes are limited to the
actual fixed destination array. The metadata-only audit pins703 static
properties including memcpy array_replace assigns and the exact postcondition:
exit0,0.227s,41908KiB,swap0,High1G/Max2G/Swap0. Native proofs use High6G/Max8G/
Swap0. Normal Kani pipeline capture confirms the same post-codegen passes as
the private runner; no missing contract-installation pass was found.

The full paired caller with that verified copy summary still timed out:
`sdk-paired-context-check-v4`, exit1,185.115s,6402236KiB,swap0. A split full
native caller check also timed out: `sdk-native-context-check-v4`, exit1,
183.868s,6408764KiB,swap0. Neither is accepted evidence. Loop metadata identifies
the remaining memcmp and small account/field-construction loops. A changed
loop configuration is being checked with unwinding assertions retained and
the same caps; no larger resource cap or unchanged full replay is authorized
by these failures. Codegen success is never reported as parent proof.

Exact remaining S2 premises: concrete native SDK/runtime heap embedding;
composition of metadata/borrow/scan/prefix/return/drop cuts into the actual
caller; actual decoder, validation, encoding and verifier child interpretations;
wrong-size and rejected-child error/log behavior; ordered oracle-log transport;
and the resulting concrete `AcceptedRunJoin` instance consumed by
`OraclePortFrozen2.dV_frozen2`. Accepted-only native contexts retain admitted
prefix/tag equations and common successful typed child replies; these must be
derived/composed, not hidden in a renamed assumption. The copy result above
closes neither those cuts nor actual whole-SDK totality. S6 still shares the
native caller gap; S1 still needs its original preparation/caller and power
range/trace joins. S1/S2/S6 and the100-bit target remain OPEN. No protocol or
security-contract decision is requested by this reference-only progress.

## Addendum 2026-10-22 — native finish errors and caller backend diagnosis

`3a32a80b7` is committed and pushed on the isolated branch. It contains the
complete owned-parent copy-loop equality above. Research HEAD
`0d1f7dbc6e198b44419c2d51660d1115428ca3e0` was then inspected read-only: both
program/adapter files still match the authoritative b2727acd3 freeze. All226
previously pinned extraction-workspace source/package files were rehashed and
still match. The revalidation is source identity only, not artifact identity.

The native finish contract now includes every reply length0..1769, all bytes
and every observed checkpoint coordinate, with the actual1768-byte RefMut
destination. It proves exact Ok/InvalidAccountData status, copied byte on
success, unchanged pre-call byte on length rejection, and the same fixed-array
write frame. The frozen block itself is unchanged; only the reference helper
borrows the Vec, keeping its owner/drop with the caller. This widens the prior
successful-length leaf instead of adding an accepted-only antecedent.
`sdk-finish-fixed-frame-join-v4`: exit0,51.150s,2338348KiB,swap0,930 properties,
3/3 covers,High6G/Max8G/Swap0. The metadata audit is read-only:
exit0,0.285s,54672KiB,swap0,1147 static properties,70 selected,High1G/Max2G/Swap0.
No total whole-stage claim follows from this bounded leaf.

Kani verified stubs require an Arbitrary return type; SDK ProgramError lacks
that implementation. The first state composition therefore stopped at
compilation. The replacement retains the exact native function and FULL SDK
ProgramError, and checks a concrete return encoder: Ok maps to true,
InvalidAccountData to false, every other original variant reaches a checked
panic. The caller reconstructs the exact original SDK result. It changes no
SDK/account carrier. `sdk-finish-fixed-frame-join-v5`: exit0,123.590s,
4633856KiB,swap0,all883 properties successful,High6G/Max8G/Swap0. Its compiled
inventory has four cover properties for three source intentions, with two
properties at the first-byte cover location; the aggregate is3/4. No claim
that every compiled cover passed is made. The packet accepts its functional
contract, records that cover qualification, and retains v4's independently
checked full-ProgramError block/three cover intentions. v5's read-only audit:
exit0,0.269s,54140KiB,swap0,1101 static properties,72 selected,High1G/Max2G/Swap0.

The source continuation candidate calls that verified borrowed helper, then
explicitly drops the owned reply before proof/public/checkpoint guards, and
reconstructs the full SDK result. The whole native/owned continuation checks
remain UNPROVED: both the arbitrary-root observation and a later checkpoint
observation still expanded to about6GiB and were reviewed/stopped. Their
sources, admissions, exact commands, stop reasons and terminal receipts are
retained. In particular the latter omits observing other root contents, so even
a future successful run needs the separately checked destination-only native
frame and full owned record-update frame composed before whole-heap equality
can be claimed. No account bytes, status, alias or drop effect is silently
removed from a claimed whole-source theorem.

The original caller SAT shape also remains excluded: tighter global40 /
memcmp689 unwinding with assertions, selected postcopy/precondition/cover
properties, and CBMC's alternate array encoding each timed out under the same
6G/8G/0 caps. These are changed proof configurations, not unchanged full Lean
replays or larger-cap retries. All safety and unwinding checks remain enabled.

A private pinned Z3 binary was installed only in the task's build-host tool
workspace (version4.15.4, exact wheel/tool hashes exported, no binaries). The
small verified-copy bridge passes the SMT backend: all142 raw non-cover
properties SUCCESS and its one cover counterexample reaches the intended
point; raw exit10 is retained. The larger SDK callers instead return conversion
error `map::at`, not a counterexample or proof. A diagnostic exception observer
(no verifier result accepted from it) locates the throw in
`smt2_convt::convert_type`, called by recursive symbol/type discovery. The
upstream6.8 converter's datatype lookup and solver profiles were inspected:
[converter](https://raw.githubusercontent.com/diffblue/cbmc/cbmc-6.8.0/src/solvers/smt2/smt2_conv.cpp),
[solver dispatch](https://raw.githubusercontent.com/diffblue/cbmc/cbmc-6.8.0/src/solvers/smt2/smt2_dec.cpp).
The flat-structure SMT profile with the SAME pinned Z3 also passes the small
bridge: all142 raw non-cover properties SUCCESS,1 reached cover,raw exit10,
0.332s,45008KiB,swap0,High1G/Max2G/Swap0. It avoids the diagnosed datatype lookup;
no Rust type, source carrier, check or security metric is changed by choosing
a different complete SMT encoding. Full caller use is still a candidate.

An exact native scan (without the previous nondeterministic scan-body cut)
was also tried and timed out; no scan-abstraction premise was discharged by
that attempt. A scalar counter-observer harness preserves all signed values,
aliases and native functions but still hits the original SMT conversion error;
it is not accepted evidence. These diagnostic paths are distinct from the
already checked total native scan/reference proofs.

Prepared GOTO copies are retained privately with source/codegen/command pins.
A later codegen can replace a warm metadata entry, so the new prepared runner
checks the original source/codegen pins, hashes the retained prepared program,
uses it read-only, and changes only the solver encoding. It verifies that the
program hash remains unchanged afterwards. Timeouts kill the whole owned child
process group, including an external solver. This is cache reuse, not a new
source freeze or a substitute for the final coherent release replay.

The capper's historical `source_revision=d8fc9...` field is an old workspace
label. It is not the authoritative protocol freeze or a claim that newly
compiled candidates existed at that revision. Exact candidate Rust source
hashes, generated source, commands and tools are in each input packet; the
actual native source blocks are checked against b2727acd3. Do not reassign a
historical proof to a different source on the basis of that legacy label.

S2 remains OPEN. The complete SDK/runtime-to-owned binding and composition of
its source prefix, child reply, errors/logs, return/drop and frame cuts into the
actual enclosing caller are still required. So are ordered oracle-log and
two-pass annotated caller transport into the concrete source instance consumed
by dV_frozen2. S6 shares that actual SDK binding; S1 retains its preparation,
original power totality/trace and caller obligations. The100-bit target is not
yet established. No production adoption or protocol decision is requested by
these source-only candidates; adopting one later requires its full equivalence,
integration and release-artifact re-pin gates.

## Native entry normalization — checked, enclosing transport still open

`sdk-call-prefix-check-v3` strengthens the complete actual native tx1-entry
cut, without fixing an initial alias map. At every reached tx1 callback it
asserts that the INITIAL data-slot map is `[0,1,2]`; the original all-alias-map,
all-signed-counter and real full statement-field inputs remain quantified.
Every one of2035 raw non-cover properties is SUCCESS and both transfer and
withdrawal covers are reached (raw cover FAILURE is the expected witness).
Raw exit10,111.855s,4413460KiB,swap0,High6G/Max8G/Swap0. Exact source/tool/codegen
and property projection are exported; the checker regenerates source and
qualification. The native functions remain literal frozen functions.

Before: the normalized parent candidate supplied `[0,1,2]` independently.
After: that relation is derived at the actual source child-entry cut over all
initial slot maps in the stated three-root format domain. This is a genuine
native caller premise discharge AT THAT CUT. Actual child interpretation and
prefix transport to arbitrary returned replies remain necessary; the cut
still returns Ok(empty Vec), causing the following length guard to reject.
The admitted proof-prefix/tag equations are explicit. No unconditional whole
SDK theorem or ordered oracle-log result is inferred from the slot assertion.

The newly normalized paired parent still timed out (v5: exit1,185.009s,
6388404KiB,swap0). A subsequent input-construction candidate removes only the
redundant self-root Rc clone/replacement/drop under `[0,1,2]` and asserts
pointer identity and strong count2 before injecting the same arbitrary signed
counters. It retains all native source functions, every SDK/owned field and
all bytes; its equivalence to the canonical input construction must remain
explicit. Its whole-parent result is not yet established.

The flat-structure SMT prefix gets past the diagnosed conversion failure but
also times out, so the backend diagnostic has not closed a source obligation.
No larger cap or unchanged full replay follows from that result. The next
source deliverable remains the complete native/owned caller binding, not a
larger collection of helper counts. S1/S2/S6 remain OPEN.

## Native complete writeback context — checked

`sdk-native-context-check-v9` executes the complete real frozen SDK stage1
through successful writeback, with the proved std-copy contract. All2178 raw
non-cover properties are SUCCESS and transfer/withdrawal covers are reached:
raw exit10,129.640s,4529696KiB,swap0,High6G/Max8G/Swap0. All reachable properties
were selected; this is not the earlier postcopy-only property subset.

Its after-call observation first checks that the actual SDK checkpoint view's
pointer equals the original root2 pointer, drops that shared guard, and reads
the same observed byte through the saved root pointer. The observed byte equals
the arbitrary full1768-byte returned checkpoint. Actual boxed/projection/public/
proof/k/None argument checks and restoration of all signed data/lamport counters
on returned paths remain in the complete native caller. This gets past the
prior empty-reply cut and establishes the native successful writeback property
at this explicitly stated context scope.

The source-entry-derived `[0,1,2]` normalization and pointer/strong-count-checked
canonical input construction are retained. Decoder/validator/encoder/verifier
hooks are still common successful full-typed replies; the native scan is still
the documented nondeterministic overapproximation. Actual child interpretation,
prefix/reply transport, runtime heap embedding and complete source/owned/error/
state/log composition remain OPEN. These facts do not disappear because the
complete native successful continuation now checks. No whole-source TOTAL or
100-bit release conclusion is asserted.

A new paired observation candidate records the actual returned phase1 Vec
pointer before moving it, checks that the complete owned parent's cell2 has
THAT pointer and length1768, checks the actual SDK checkpoint pointer/length,
and only then compares bytes through the two bound pointers. Both complete
executions and all prior SDK/owned metadata/counter checks remain. This changes
only ghost observations, not either carrier or source implementation. It is
terminal with timeout (v7: exit1,185.503s,6470816KiB,swap0); no paired
result is established. The prior self-root input
construction candidate v6 timed out: exit1,184.989s,6387744KiB,swap0,6G/8G/0.


## Borrowed-buffer reference: checked scan and acquisition seam (2026-10-22)

The paired borrowed-buffer candidate v9 also timed out: exit1,185.915s,
6440172KiB,swap0,High6G/Max8G/Swap0. This does not discharge whole-stage
correspondence. No increased cap or identical rerun is proposed. Its source,
codegen and terminal resource receipts are retained; v8's dependency-alias
codegen failure is retained separately and is not accepted proof evidence.

`owned-sdk-borrowed-v1` reborrows buffers already owned by the complete SDK
reference. It retains all thirty SDK/protocol types and all twelve Ops fields,
checked literal-equal by `adapt-sdk-borrowed.py`, without an opaque SDK carrier.
The short decoder borrow ends before unchanged validation, encoding and proof
acquisition; the verifier then reborrows the original public and proof Vecs.
Charon/Aeneas extraction succeeded under the capped host policy. The adapted
complete reference compiled locally as `S2SdkBorrowedReferenceV1`: exit0,
14.409653333s,2283601920 bytes RSS,swap0. This is a candidate reference;
complete original/new body equivalence is still a required gate.

Two subsequent kernel proofs address that gate directly:

- `S2SdkBorrowedScanV1.borrowedScan_eq_sourceScan` proves TOTAL equality of
  the candidate's complete borrowed checkpoint scan subcomputation and the
  previously checked actual-source iterator scanner. Invalid slots, all-zero
  and nonzero buffers are included. No scan-success, range or all-zero premise
  remains. It reuses the established source iterator proof rather than proving
  parsing or multiproofs again. Focused receipt `s2-sdk-borrowed-scan-v2`:
  exit0,10.544526166s,2244132864 bytes RSS,swap0.
- `S2SdkBorrowedBufferFrameV1.acquire_reborrow_eq` equates the complete
  emitted shared-acquisition/re-read/continuation subcomputation with the
  original acquisition/captured-buffer continuation. The sole reached-read
  premise is the earlier actual public cell read; there is no assumed
  acquisition success, slot range, byte frame, nonalias condition or increment
  range. The full SDK passed to the continuation and all Result failure,
  divergence and ordinary error behaviour are retained. Its byte-read frame
  includes invalid queried slots and arbitrary acquired/queried aliases.
  Focused receipt `s2-sdk-borrowed-buffer-frame-v7`: exit0,12.179691417s,
  2213330944 bytes RSS,swap0. This discharges the acquisition byte-preservation
  premise at this seam, not the enclosing stage-1 theorem.

All three local targets used the atomic local lock, `-j1 -M4400`; accepted
`#print axioms` output contains only `propext`, `Classical.choice`, `Quot.sound`.
Failed local drafts and their exit statuses are retained and excluded by the
source-hash/current-success receipt selector. No unchanged full replay ran.
The packet checker regenerates the borrowed Rust source and Lean adaptation,
checks successful capped extraction receipts and pins tools/imports separately.
No compiled artifacts are distributed.

Next enclosing deliverable: consume the scan equality and acquisition/re-read
continuation equality in the *complete* old/new emitted stage1 body and outer
release theorem, with every error/state effect preserved. This is not yet
proved. Actual native heap embedding, typed child/scan/prefix/reply
interpretation, and ordered/two-pass caller composition remain OPEN after it.
S1 and S6 retain their previously documented shared caller premises; neither
is promoted to closed by these S2 seams. No production source decision or
adoption is made. Re-pin/equivalence obligations remain explicit if a source
candidate is eventually adopted. Read-only research revision
`82df37dd2b8a1f3d68aed4421e5507be0dfd6a76` retains byte-identical shipped program
and adapter files against freeze `b2727acd3abf79315d18b754a260f58f4b1c6326`;
the two-file comparison is separately recorded, not a whole-dependency replay.
The 100-bit per-attempt target remains not yet established.

Final consistency audit selected 58 current source targets and pinned 11766
cached import objects; these are evidence consistency counts, not security
closure counts. No unchanged formal replay was run. `git diff --check` reports
only preserved upstream extraction/log whitespace (including the literal adapted
reference emission); raw evidence and its recorded source hashes are retained.


## Complete borrowed-reference equivalence gate — closed (2026-10-22)

This addendum supersedes the preceding "complete original/new body equivalence"
and "Next enclosing deliverable" open items, only at their owned-reference scope.
`S2SdkBorrowedEquivalenceV1.body_eq` now proves, with **no propositional
premise**, for arbitrary full `Ops`, program, SDK, data and live guards:

```
BorrowedReference.owned_stage1_body ops program sdk data guards
  = owned_stage1_body ops program sdk data guards
```

`stage1_eq` proves, again without a success, range, frame, nonalias or child
execution premise:

```
BorrowedReference.owned_stage1 ops program sdk data
  = owned_stage1 ops program sdk data
```

The second equality includes the complete outer reverse guard release. These
are unconditional full `Result` equalities: ordinary statuses, all SDK fields,
failure and divergence are retained. They are not termination theorems for
arbitrary external child Ops. They neither replace the SDK carrier nor turn
an assumed byte frame into a field of a new contract.

The prior gate consisted of two isolated equalities (scan and acquisition
frame) plus an unproved requirement to use them in the complete caller. The
new full-body proof walks each common source operation under the checked
`bind_congr_reached` rule. At each inserted public re-read, it consumes the
actual preceding read and acquisition equations to derive a successful
re-read of the same bytes. The source supplies its own queried-slot validity
and frame; no independent range/acquisition/scan/decode success is added to
`body_eq` or `stage1_eq`. Both instruction branches and all error continuations
are included. The kernel checks every generated proof term.

`stage1_current_first` consumes this equality in the existing enclosing
installed decoder/verifier theorem. Its only execution premise is one complete
borrowed `owned_stage1 (Installation.install ops verifierOps)` success. Its
conclusion includes an actual decoder success and the corresponding current
`firstCurrent` execution on the same public bytes; there is no independent
parse, projection or verifier-child success premise. This conclusion is
ACCEPTED-ONLY and still concerns the full owned reference. `ops.op10` (Solana
digest), `ops.op11` (exact verifier error/log interpretation), and the explicit
current verifier `verifierOps` retain their source-instance obligations; the
reference theorem does not hide or instantiate them. The earlier current
verifier installation/dependency inventory is unchanged.

The first broad comparison hit the unchanged default200000 heartbeat limit.
The replacement compares only the next source operation, reduces only outer
control structure and consumes the named byte-frame/scan results. No heartbeat,
recursion or memory limit was increased. Draft compiler errors and terminal
receipts are retained and excluded from the accepted current-source selector.
The smallest changed target compiled before packet/hash audits. No new heavy
host job or unchanged full regression was launched for this proof.

**Remaining S2 boundary:** actual frozen AccountInfo execution to the full owned
reference, including concrete runtime heap construction, the remaining
native scan/prefix/reply/child interpretation and exact errors/logs/state, plus
ordered oracle/two-pass caller transport. The earlier native typed-callee cuts
and successful writeback certificate remain scoped certificates, not this
missing whole-source instance. This gate closes a real enclosing reference
obligation but does not close S2 or the shared actual-SDK S6 obligation. S1
retains the previously documented original preparation/powers/trace gates.
There is no production source change or adoption decision in this commit;
a future production candidate would still require its source/artifact re-pin.
The 100-bit per-attempt target remains not yet established.

Final focused receipt `s2-sdk-borrowed-equivalence-v12`: target
`S2SdkBorrowedEquivalenceV1`, exit0, 22.873708792s,
3227238400 bytes RSS,swap0. All three `#print axioms` reports
(`body_eq`, `stage1_eq`, `stage1_current_first`) contain only `propext`,
`Classical.choice`, `Quot.sound`. Source/tool/direct-import hashes and exact
`lake env lean -j1 -M4400` invocation are in the receipt/command packet.


## Stage1 proof-prefix guard: native checked frame and enclosing reference join

The native contexts above seed the688-byte candidate prefix and tag696=2.
The new gate removes that restriction *at the isolated source-fragment
boundary*. `sdk-proof-gate-v1::native_gate` contains the exact frozen stage1
statements from `let proof_length = verifier::PROOF_BYTES` through the complete
length/prefix/tag rejection condition. It takes an actual SDK `Ref`, retains
full `ProgramError`, and returns the exact `(proof_start,proof_end)` on success.
Its scalar reference is extracted from that same checked Rust crate. No scan,
decoder, validator, encoder or verifier hook is used in this certificate. No
canonical parser or multiproof work owned by the lead is redone.

`sdk-proof-gate-join-v2`: exit0,132.314s,2718772KiB RSS,swap0; all773 assertions
pass. For every58296-byte storage array, every length0..58296, every688-byte
candidate and arbitrary SDK metadata, the exact native guard and scalar
reference agree on their complete result, including prefix/tag/length errors.
The function retains the SDK buffer pointer/length and live borrow counter.
The harness-selection v1 failure ran no proof and remains excluded.

`sdk-proof-gate-frame-v1`: exit0,146.047s,3578036KiB RSS,swap0; all826 assertions
pass. This additionally proves the exact guard's **empty modifies set**, not
just matching selected observations. Both native guard bodies and both scalar
reference/helper bodies are byte-equal between the two checked crates; only
the native contract annotation/harness kind differ. There is no unproved
contract stub. Source ownership, actual SDK types and all ordinary returned
error variants are retained.

Both jobs use High6G/Max8G/Swap0, one optimized Kani job and unwinding assertions.
Each reports4/5 compiled covers. The compiler duplicates the prefix-mismatch
source location: four original source cover intentions yield five properties.
The accepted claim is all functional/frame assertions passing, not every cover
or per-location reachability. Fresh metadata-only v2 audits select the exact
harness kind and original line, pin the proof input/program/metadata, and show
the assigns properties. An attempted metadata audit reused an existing output
name and stopped before execution; its v1 output is not the selected audit.
The successful v2 audits run no solver replay.

The10MiB wrong-length native candidate was reviewed and stopped at
167.862s,6400316KiB,swap0: encoding a huge symbolic allocation for a path that
should reject before byte access reached about6.4GiB. It establishes nothing;
its source, stop reason and terminal receipt are retained and excluded.
No larger cap or unchanged rerun follows. In particular, the native guard
certificate is **not** advertised for every runtime length up to10MiB.

The following Lean results consume the new reference and complete caller:

- `S2SdkProofPrefixTotalV1.prefix_total`: TOTAL comparison at every representable
  pair of slice lengths. Every read and increment is derived; the exact Boolean
  means the candidate fits and every consumed byte agrees. No loop/index/add
  success is supplied. The proof decreases remaining candidate length.
- `S2SdkProofGateTotalV1.gate_total` and `wrong_length_reject`: TOTAL full reference
  gate, including all wrong lengths and exactly the Ok/InvalidAccountData image.
  Checked688+57607=58295,688+8=696 and the reached-length tag-index bound are
  discharged. This all-length theorem is for the extracted reference, not an
  extension of the stopped native10MiB job.
- `S2SdkProofComparatorV1.scalarNe_eq_standard`: exact full-Result equality of the
  scalar loop wrapper and the installed standard U8 slice comparator, for all
  contents and lengths. The generic List proof reuses each primitive U8 result;
  no concrete688-cell kernel normalization is used.
- `S2SdkProofPrefixParentV1.body_eq_loop` and `stage1_eq`: the **complete installed
  owned stage1** consumes that equality at both real comparison sites, including
  all errors, SDK fields and final reverse guard release. No prefix/tag pass,
  comparator/child success or range premise remains in these equalities. These
  are unconditional Result equalities, not termination of arbitrary child Ops.
- `S2SdkProofGateJoinV1.caller_prefix_eq`: the full-buffer scalar reference loop
  is the same comparison as the actual reached Vec prefix-range operation in
  the complete caller. It consumes the existing exact frame-operation theorem;
  the reached58295-byte length supplies its range bound.
- `stage1_borrowed_eq` then binds that complete scalar-comparison caller to the
  already checked full borrowed SDK reference, with no execution premise.
  `stage1_current_first` consumes the equality in the enclosing installed caller
  theorem: one complete reference success supplies actual decoding and current
  `firstCurrent` on the same public bytes, without independent parse/projection/
  verifier-child success. This last theorem is ACCEPTED-ONLY at reference scope.

Before, the full owned caller reached the standard slice comparator, while
only native contexts with matching seeded prefixes were checked. After, both
full reference caller branches are equated to the total scalar loop, that loop
is connected to their exact prefix slice, and the isolated actual SDK guard
is checked against the same extracted scalar reference with arbitrary prefix/
tag bytes and no write effects. The complete native caller theorem has **not**
been inferred from the isolated guard. Native-to-reference descriptor/runtime
embedding, native higher-length rejection, actual child/scan/reply interpretation,
exact error/log binding and ordered oracle/two-pass caller transport remain.
`ops.op10`, `ops.op11` and current verifier Ops retain their previously stated
source-instance obligations. S2 and the shared actual-SDK S6 gap remain OPEN;
S1 retains original preparation/powers/caller obligations. No production source
or adopted wire parameters change, and there is no new source-adoption decision.
Any future adopted source candidate still requires full equivalence and re-pin.
The100-bit per-attempt target is not yet established.

Focused local checks use the atomic lock, `-j1 -M4400`, source/tool/import hashes,
zero swaps and only standard axioms. A foreign S4 local job held the lock during
one wait; it was left untouched. No unchanged full regression was run. Pins and
raw source-only extraction evidence are in the packet; no binaries are exported.

| Smallest changed target | Selected receipt | Exit | Wall seconds | RSS bytes | Swap |
|---|---|---:|---:|---:|---:|
| `S2SdkProofGateModelV1` | `s2-sdk-proof-gate-model-v2` | 0 | 8.359057 | 3204907008 | 0 |
| `S2SdkProofPrefixTotalV1` | `s2-sdk-proof-prefix-total-v2` | 0 | 26.295021 | 3226615808 | 0 |
| `S2SdkProofGateTotalV1` | `s2-sdk-proof-gate-total-v4` | 0 | 20.781145 | 3240050688 | 0 |
| `S2SdkProofComparatorV1` | `s2-sdk-proof-comparator-v3` | 0 | 19.798327 | 3116613632 | 0 |
| `S2SdkProofPrefixParentV1` | `s2-sdk-proof-prefix-parent-v3` | 0 | 10.617364 | 3255484416 | 0 |
| `S2SdkProofGateJoinV1` | `s2-sdk-proof-gate-join-v2` | 0 | 12.727309 | 3158392832 | 0 |

Read-only research inspection at `a72cb615acf11f76a867cee282465c17df20eae9` confirms both shipped files
remain byte-identical to freeze `b2727acd3abf79315d18b754a260f58f4b1c6326`. The latest handoff's13:05 update
still names `OraclePortHeadlineFrozen2PerAttempt.final_soundness` and the
matching `dV_frozen2` stages. No older query-normalized headline is substituted
for the raw per-attempt contract, and no freeze is inferred from research
proof commits.

Host receipt `source_revision` remains the generic runner's historical
`d8fc9db...` marker; it is not the new candidate or frozen-source revision.
The source-cut freeze and exact input SHA, Cargo lock, tool pins and matched
function bodies identify the checked sources. The superseded frame-property
v1 input was rewritten before an output-name preflight rejection; it is
explicitly unselected. Fresh v2 audit pins are used. Final consistency audit
selects65 current source targets and11773 cached import objects. These counts
are consistency evidence, not security closure; a coherent release replay
remains required.

## 22 October continuation: native wrong-length frame and observer emission

Read-only research inspection at `23392f8056c0fd9d2376d147d7f5ecb97f033aba`
still finds both shipped program/adapter files byte-identical to freeze
`b2727acd3abf79315d18b754a260f58f4b1c6326`. The handoff's latest23:35
dependency addendum retains S2 caller binding as a dependency of the lead's
cones. The adopted endpoint remains
`OraclePortHeadlineFrozen2PerAttempt.final_soundness` against `dV_frozen2`.

The isolated native guard now has a checked **all-wrong-length empty frame**:
`sdk-proof-length-frame-cut-v2`, raw CBMC exit10,14.556s,1322392KiB RSS,swap0.
All809 non-cover properties pass, including23 assigns properties, frees,
contract postconditions and unwinding checks. Both covers are reached (raw
CBMC reports their witnesses as FAILURE). Every slice length0..10485760
except58295 rejects with the actual InvalidAccountData result. The sole
additional body cut replaces `memcmp` with assert(false);assume(false), whose
assertion passes: the comparison is proved unreachable, never assumed equal.
The actual SDK Ref, full ProgramError and frozen guard statements remain.

This complements `sdk-proof-gate-frame-v1` for the matching length and closes
the native guard's explicit0..10MiB **component** domain. It removes the
higher-length restriction at that component boundary. It does not discharge
runtime heap/descriptor embedding or the enclosing native caller premise.
The extracted scalar reference's TOTAL Lean result is reused unchanged.

The first reconstructed frame attempt (`sdk-proof-length-frame-cut-v1`)
omitted the normal Kani contract enforcement pass. Metadata audit v1 caught
the absence of assigns properties; its functional assertions alone are not
frame evidence and it is excluded. V2 adds the exact metadata-selected
`--dfcc <harness> --enforce-contract <contracted-function>` before library
addition, as in the pinned Kani driver. Fresh properties audit v2 pins the
same ready program, receipt, source and809 passing properties. Earlier cut
attempts, the missing-libc failure and incomplete metadata audit remain
excluded. Normal Kani libc source is exported alongside its SHA pin.

The paired caller diagnostic exposed a genuine **emission discrepancy in
this Kani context**, not an established production-source counterexample:
native `observer()->verifier::Observer {None}` is emitted as a load from the
mutable harness `proofs::OBSERVED` allocation. This is already present in raw
compiler output before custom linking. A new proof in the unchanged full
crate reproduces it through normal cargo-kani: `observer-emission-check-v2`,
exit1,0.751s,188600KiB,swap0; exactly the literal-None assertion fails among20
checks after an arbitrary ghost write. A standalone small Option<fn()> test
passes, so no blanket claim about every Kani compilation is made.

`prepare-sdk-ghost-storage.py` wraps each harness-only mutable global in an
allocation with a distinct tag and projects the same value at every access.
All initial ghost values, symbolic input domains, contracts and assertions
remain; the entire source prefix before cfg(kani), including stage1,
first_decoded and observer, is byte-identical. The corresponding normal
reproduction (`observer-emission-check-v3`) passes all20 checks: exit0,
0.670s,189068KiB,swap0. Raw paired-context audit v2 confirms both actual
observer bodies load the same **const** eight-zero-byte allocation, with no
ghost read. This is a harness remedy plus focused emission evidence, not a
general repair proof for Kani or a complete source/caller theorem. No observer
assertion is removed, no None premise is assumed, and no tool/source candidate
is adopted into production.

Relevant upstream Kani0.67.0 source is retained with URLs and hashes under
`tool-and-freeze-pins/kani-0.67.0-source`: allocation caching in operand.rs,
static registration in static_var.rs and the driver contract-enforcement
sequence. It informs diagnosis; the installed tool binaries retain their
separate pins. There is no unreviewed compiler patch in these checks.

`memcmp-equal-join-v1` also checks a scoped leaf through normal Kani/libc:
equal688-byte owned arrays at the same start or in distinct objects give0
with an empty write set, exit0,9.525s,397304KiB,swap0. This is not an arbitrary
overlapping-heap lemma. The attempted C specialization must assert readable
regions, the checked layout class and all688 equal bytes. Its first array
equality encoding incorrectly compared whole root arrays despite a cast;
it is excluded. The revised diagnostic copies each prefix into an actual
fixed local array before asserting equality. Its model transport remains
unproved and the paired run `sdk-paired-equalcmp-check-v5` times out:
exit1,187.022s,6391060KiB,swap0. It establishes no caller correspondence.
No unchanged rerun or larger memory cap follows. The next caller check must
split the buffer-byte/frame step from stage control and compose the checked
steps, rather than retrying the whole-stage formula.

Before/after enclosing obligation: the actual native-to-owned stage1 binding
premise is **unchanged**. Native guard range/frame coverage improves and the
observer discrepancy is isolated without weakening its assertion. Still
required are concrete SDK/runtime descriptor embedding, installed child and
scan/reply joins, exact error/log effects, and ordered two-pass oracle/caller
transport. `ops.op10`, `ops.op11` and verifier Ops retain their stated source
instance obligations. S2, shared actual-SDK S6, and original preparation/powers/
caller S1 remain OPEN. The100-bit per-attempt target is not yet established.

All new solver/metadata jobs use fresh host admission and explicit cgroup
caps with MemorySwapMax=0; no local Lean source changes or replay were needed.
The previous65-target Lean evidence and standard-three-axiom audits are
reused, not rerun. `#print axioms` is N/A for these Kani/metadata jobs.
Exact source/tool/input/resource/terminal receipts are source-only in the
packet. Custom exit10 is never relabelled as a normal cargo-kani success.
`git diff --check` reports only preserved whitespace in raw diagnostic/compiler
logs; those evidence bytes are kept unchanged. Source and prose have no new
whitespace findings.

## Complete rejected-run buffer frame and tagged native caller recheck

The new enclosing theorem is
`ErrorBufferFrame.stage1_error_buffers` in `S2SdkErrorBufferFrameV1.lean`:

```
∀ ops program sdk out data error,
  owned_stage1 ops program sdk data = ok (.Err error,out) →
  buffers out = buffers sdk
```

`buffers` is the complete list of byte vectors, including their lengths.
The theorem covers every ordinary ProgramError return of the **complete
emitted owned stage1 and exact reverse-release finalizer**, for arbitrary
child Ops and SDK values. It supplies no separate acquire/release success,
slot validity, counter range, byte equality or child-success premise. The
source body has exactly one byte-vector assignment, followed by an Ok return;
an Err execution cannot take that terminal branch. Reached acquisitions and
release steps preserve bytes, and the checked proof composes their frames
through all actual body branches. `release_buffers` itself needs no separately
assumed live-guard invariant: its ordinary-return equation derives the reached
indexes and setters. This is a **RETURNED-ERROR frame theorem**, neither
unrestricted TOTAL termination nor an accepted-success theorem.

Before, only helper-level acquisition byte frames were available. After,
`body_error_buffers` derives the same full frame from one complete body error
return, and `stage1_error_buffers` includes final release. The dependent
`S2SdkErrorBufferJoinV1.lean` consumes the previously proved complete caller
equalities: `borrowed_error_buffers` covers the complete borrowed reference;
`installed_error_buffers` covers the installed scalar-comparison/current
decoder/verifier caller; `installed_error_read` derives equality of each
byte-vector read, retaining invalid-slot failure and all aliases, with no
queried-slot range premise. These are reference results. The actual native
SDK embedding is not silently supplied by them.

Smallest-file/following-bridge receipts, atomic local lock, `-j1 -M4400`:

| Target | Selected receipt | Exit | Wall seconds | RSS bytes | Swaps |
|---|---|---:|---:|---:|---:|
| `S2SdkErrorBufferFrameV1` | `s2-sdk-error-buffer-frame-v4` |0|19.934187|3225075712|0|
| `S2SdkErrorBufferJoinV1` | `s2-sdk-error-buffer-join-v1` |0|20.673901|3217375232|0|

All ten axiom reports contain only propext, Classical.choice and Quot.sound.
The first three focused frame attempts fail on finalizer elaboration (empty
dsimp, field projection cases and unreduced successful-constructor equations).
Their exact sources/logs are retained; compiler recovery sorryAx output in
those failed receipts is excluded. No source contains sorry, a custom axiom,
native_decide or a resource-option override. No unchanged full replay runs.
The accepted source/import audit now selects67 targets and11775 objects; this
is consistency evidence, not release closure.

The native caller's tagged-ghost successor also passes:
`sdk-native-context-check-v10`, raw exit10,131.972s,4521912KiB RSS,swap0,
**2176/2176 non-cover properties SUCCESS and2/2 covers reached**. It executes
the same complete frozen native stage1 as v9, with actual AccountInfo/RefCell
state, both full typed statement variants, all returned1768 checkpoint bytes
through an arbitrary observed coordinate, exact first-decoded argument
pointers/lengths/semantic references/k/None, returned checkpoint descriptor
and borrow-counter restoration. There is no selected-property filter.
The only harness change wraps ghost globals in distinct tagged allocations;
the complete source prefix before cfg(kani) is byte-identical to v9.

`sdk-native-observer-emission-properties-v1` pins that exact caller artifact
and confirms its native observer body loads a const eight-zero-byte allocation,
not mutable ghost storage. It is metadata-only, exit0,0.296s,46976KiB,swap0.
Because tagging also changes the ghost getters used by the copy contract,
the same crate's **actual** `std_copy_value_frame` proof_for_contract is checked
again: `sdk-native-tagged-copy-contract-v1`, normal cargo-kani exit0,9.561s,
444028KiB,swap0, all assertions and both covers pass. The changed primitive
binding is not silently attributed to the historical leaf. The older native
v9 remains retained and checked as historical evidence; v10 replaces it in
the selected native caller cut.

The native scope has **not** expanded: common successful decoder/validator/
encoder/verifier replies are still explicit typed child hooks; seeded
candidate-prefix/tag, concrete scan interpretation, source-entry descriptor
normalization, canonical constructed Rc graph versus arbitrary valid runtime
heaps, actual child installation, and full state/log/oracle transport remain
composition obligations. This is a checked enclosing native caller context,
not an unconditional source-to-owned equivalence or whole S2 closure. Its
observer assertion is derived and emission-audited, never assumed or removed.

The attempted paired decoder-entry prefix contexts are all **excluded**:

| Attempt | Encoding/change | Exit | Wall seconds | RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| decoder-entry-v1 | Arbitrary byte queries; reviewed/stopped |15|168.391|6387496|0|
| decoder-entry-v2 | Descriptor/counter queries only; timeout |1|184.026|6390240|0|
| decoder-entry-v3 | UF array encoding; reviewed/stopped |15|136.952|6373100|0|
| decoder-entry-v4 | Inventory-based unwind40, all unwinding assertions; timeout |1|184.139|6391020|0|

All use fresh host admission, High6G/Max8G/Swap0. The loop inventory is
metadata-only and retained. Stopped handles are verified against their live
process command lines before signalling; terminal receipts and voluntary-stop
reasons are preserved. None supplies a prefix join, byte-frame proof, array
encoding equivalence claim or successful caller execution. No raised memory
cap or unchanged rerun follows. Constructing and running both whole SDK heaps
remains expensive even before decoder success. The next native composition
must start from an already-related symbolic SDK state and check one concrete
buffer/call continuation step with verified callees, then compose the steps;
another whole paired prefix fixture is not the next gate.

Read-only research inspection at `45c7b3c00a7431e66833a51686b8715d355749a3`
confirms the two shipped program/adapter files still equal the authoritative
freeze byte-for-byte. No production source or other cone is modified. There
is no new adoption/re-pin decision requested by these proof/harness changes.
S2 remains OPEN for the actual runtime/source/caller and ordered two-pass
joins; S6 shares that native boundary and S1 retains original preparation/
gamma-powers/caller obligations. Ops10/SolanaDigest, Ops11/exact error/log
mapping and verifier source instances remain explicit. The100-bit per-attempt
target is not yet established.

### Native caller Rc input-domain premise removed

The selected native context is further widened, rather than stopping at
constructor-derived Rc inputs. `prepare-sdk-native-rc-domain.py` leaves the
entire source/helper/contract prefix before `native_parent_arguments` byte
identical to the tagged native v6 context. Only the harness's logical input
state is widened: it validates each data/lamport Rc header projection against
the actual SDK strong/weak getters, saves the constructor values, injects
arbitrary nonzero header fields, checks getter correspondence, executes the
unchanged complete source body, checks every injected Rc field unchanged on
return, and restores all constructor fields before any harness handle drops.
It reuses the exact two-word RcInner projection already checked in the wider
SDK primitive frame certificates; it does not substitute an SDK carrier.

The first widened context (`sdk-native-context-check-v11`) checks all twelve
fields in1..isizeMAX: exit10,165.466s,4634896KiB,swap0, all2548 non-covers
pass and all4 covers are reached. This is retained as a checked intermediate,
not advertised as the full Rc domain. Inspection of the Rust source associated
with pinned compiler53732d5e0 shows Rc increments wrap and abort on zero,
with no isizeMAX cutoff. The source and URL/SHA are retained; installed
compiler/sysroot archive hashes are separately recorded, rather than asserting
that an upstream source download proves their binary provenance.

The final selected successor, **`sdk-native-context-check-v12`**, therefore
checks **every nonzero usize** independently for all three data strong counts,
three data internal weak counts, three lamport strong counts and three lamport
internal weak counts. Public weak count is internal weak minus1. There is no
upper-half exclusion: the only injected-count predicate is count>=1.
Raw exit10,180.287s total runner wall,4623192KiB RSS,swap0; **2546/2546
non-cover properties pass and5/5 covers are reached**, including successful
source execution at strong1, strongusizeMAX, and internal weakusizeMAX.
The actual solver command completes within its individual180s deadline;
the reported total wall also includes preparation and result processing.
All original caller arguments, actual SDK guard effects, arbitrary checkpoint
byte and returned-descriptor checks remain enabled. Rc preservation checks
run regardless of adapter status within the same explicit common-successful-
child context. No source or assertion is removed to widen the domain.

Before, the native accepted-caller certificate used constructor-derived Rc
counts. After, the exact same native source is checked at every nonzero Rc
header value, with field/getter correspondence and restoration checked. This
discharges that **scalar Rc-count restriction in the enclosing native caller
context**. It does not prove general heap relocation/runtime embedding, actual
child identities, scan/seed/alias normalization composition or ordered oracle
transport. The broader valid-runtime relation still needs its concrete join.

The observer's exact new artifact is independently emission-audited:
`sdk-native-full-rc-observer-emission-properties-v1`, exit0,0.294s,
48960KiB,swap0, const-None read with no ghost dependency. The same full-context
crate's actual copy proof_for_contract is also checked again after this
context change: `sdk-native-full-rc-copy-contract-v1`, normal cargo-kani exit0,
9.953s,444292KiB,swap0; all assertions and both covers pass. That source's
complete copy helper, contract, ghost getters and primitive-proof prefix are
byte-identical to v6. The manifest selects v12 and this matching leaf in place
of v10 and its leaf, retaining all predecessor receipts. A streamed metadata
inventory additionally pins installed core/alloc/std and Kani archives; binary
payloads are not distributed (62 archives,261351858 bytes hashed). A fresh
post-check revalidation confirms all226 retained relevant source/package
files on the NUC still equal the authoritative b2727acd freeze. This is a
source-byte check, not a frozen SBF artifact rebuild.

The enclosing rejected-run Lean theorems above remain the new reference-side
frame result. There is no new theorem claiming complete native-to-owned
stage1 equality. Lean receipts record base revision e4bccb2a3 plus exact new
source snapshots/SHA values; those exact snapshots are included here.

### Unseeded native caller and enclosing same-buffer gate witness

The selected complete native caller now removes the harness's proof-prefix/tag
initializer altogether. `prepare-sdk-native-unseeded.py` deletes exactly the
raw copy688/tag696 assignment from native v8 and adds no assumptions. The
complete source/helper/contract/ghost prefix before `native_parent_arguments`
is byte-identical. Every original assertion and all twelve arbitrary nonzero
usize Rc fields remain; proof58295, public1880, checkpoint1768 and encoder
candidate688 are independent arbitrary input arrays. Invalid prefix/tag runs
are handled by the unchanged source guard. No initializer-equivalence premise
is needed for this new caller domain.

**`sdk-native-context-check-v13`**, source `sdk-native-context-v9`, checks all
2546 non-cover properties SUCCESS and reaches all5 covers (raw CBMC exit10,
not relabelled exit0),167.756s,4366072KiB peak RSS,swap0. This genuinely removes
the seeded-prefix/tag restriction from the enclosing checked native context.
The source gate, account operations, same-buffer typed child argument checks,
observer assertion, successful checkpoint byte writeback and returned borrow/
Rc scalar checks are retained. The matching copy leaf is reused from v8 only
after checking the **entire unchanged helper/ghost/contract prefix**, including
its proof_for_contract function, byte-for-byte. No unchanged leaf/full replay
is run. The exact new raw observer artifact is independently audited in
`sdk-native-unseeded-observer-emission-properties-v1`: exit0,0.286s,
48844KiB,swap0; it loads const None, without a mutable ghost dependency.

The checked Lean reference also derives its own gate rather than accepting
independent prefix/tag hypotheses:

- `S2SdkGateAdmittedImageV1.admitted_cells` derives length58295, every one of
  the688 exact candidate-prefix cells and tag696=2 from the actual extracted
  `reference_gate` success. `admitted_seed_fixed` proves the mathematical
  prefix/tag image equals the original byte at **every Nat coordinate**,
  including invalid indices and the untouched suffix. This is ACCEPTED-ONLY;
  the previously checked `gate_total` remains the separate TOTAL theorem.
- `S2SdkAdmittedCallerV1.caller_guard` identifies the actual emitted Vec prefix
  range/comparator/tag operations on one Vec with the full-buffer gate.
- `stage1_guarded_first` consumes **one complete installed reference stage1
  success, including its final release**, and derives one joint witness:
  the very same proof Vec's [688,58295) range is passed to its reached
  `first_decoded`, its matching candidate passes the extracted gate, and its
  prefix/tag image is identical at every coordinate. No independent comparator
  success, tag match, prefix validity, child success or fixed-point premise
  appears in the enclosing theorem. The witness does not expose a separate
  statement/encoder-source equality; that richer shared-decoder/encoder join
  remains a next strengthening, rather than an implied claim.

The final focused receipts are `s2-sdk-gate-admitted-image-v3` (exit0,
14.655595s,3238952960B RSS,swap0, two standard-only axiom reports) and
`s2-sdk-admitted-caller-v6` (exit0,25.305688s,3231727616B RSS,swap0, two
standard-only reports). Earlier failed elaborations are retained and excluded:
reserved identifier/coordinate coercion errors in the first file; scalar
constant/condition normalization and an expensive generic continuation search
in the second. Its v5 hits the default200000 heartbeat limit; v6 uses symbolic
checked-add facts, targeted scalar/boolean normalization and direct premise
selection, with **no resource-option override**. A failed compiler's error
recovery axiom lines are not accepted proof evidence. The successful packet
checker selects69 current Lean targets and21 SDK cuts, not a whole-cone replay.

The abandoned initializer approach is explicitly **not proved**:

| Attempt | Changed encoding | Exit | Wall seconds | RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| sdk-seed-join-v1 | Whole proof-array coordinate postcondition; stopped |1|199.483|6407372|0|
| sdk-seed-join-v2 | Typed688-byte prefix view; stopped |1|226.682|6412944|0|
| sdk-seed-frame-v3 | Write-frame/tag only; stopped |1|88.964|6387628|0|
| sdk-native-context-check-v14 | Added arbitrary proof/public/checkpoint frame queries; timeout |1|183.982|6388764|0|
| sdk-native-context-check-v15 | Only extra rejected-checkpoint byte query; timeout |1|184.095|3433992|0|

These runs use fresh admission, High6G/Max8G/Swap0. Their sources, stops,
receipts and diagnostics are retained. They establish no initializer or added
native frame assertion; no cap was raised. The exact unseeded caller result
v13 supersedes the need for initializer transport, not the failed checks'
status. The first property-inspector metadata (`sdk-seed-properties-v2`)
incorrectly described a successful proof receipt. It is **superseded/excluded**:
`sdk-seed-properties-v3` explicitly says its metadata establishes no assertion
or write-frame property. The failed attempted metadata rerun hit the immutable
receipt-directory guard; only the v3 corrected audit is used. No seed audit is
included among accepted SDK cuts.

Read-only research inspection also found adoption merge29cbab431 for the
other owner's three S4 source files. `research-caller-readonly-20261022.json`
records the observed research revision and exact working/commit/frozen hashes.
The program adapter/first, verifier and candidate files still match b2727acd;
weights/fast_dots/fast_pairing have changed. This packet does **not** silently
re-pin those other-owner dependencies or claim the old S4/from_fn results for
the newly adopted implementation. The retained b2727acd component target and
all226 host-source checks remain explicit. Consolidated source/artifact
re-pinning must account for the adopted S4 change and affected S1 powers
caller, with that owner's equivalence/adoption gates; this local S2 progress
changes no shipped source or security contract.

S2 is still OPEN: fixed public/checkpoint native lengths, common successful
actual typed child hooks, pure scan abstraction, canonical data/lamport slot
construction and runtime heap transport remain in the native context. Concrete
child implementation installation, general native-to-owned correspondence,
full errors/logs/state and ordered oracle transport are not discharged here.
The complete reference rejection-buffer theorem remains valid but the new
native rejected-checkpoint byte frame was **not** established by v14/v15.
S6 and S1 retain the shared actual caller boundary; no whole S1/S2/S6 or
raw100-bit per-attempt closure is claimed. The next concrete work is a shared
source decoder/encoder/gate/first witness and compositional native-state
transport; another unchanged whole-array or paired-stage replay is excluded.

### 2026-10-22 — shared decoded-statement/encoder/gate/current-first witness

The previous next strengthening is now checked for the complete **reference**
caller. `S2SdkLinkedCallerV1.stage1_linked_first` and
`owned_stage1_linked_first` consume one enclosing successful stage1 execution,
including its reverse finalizer. Their `LinkedFirst` conclusion contains one
boxed decoded statement, its actual common and semantic-public projections,
its candidate encoder output, the same proof Vec's suffix range and full
admission gate, and the reached `first_decoded` call on those public/proof
bytes. No child-success, independently selected candidate, parse-match,
prefix/tag or seed-fixed-point premise is supplied separately. Targeted
normalization of the reached original `map_err (Ok candidate)` preserves the
actual candidate value across the error mapper; the mapper is not replaced.
This strengthens the earlier `GuardedFirst` conclusion without changing its
accepted-run quantification or carrier. It does not yet identify these
existential buffers with an arbitrary native SDK heap.

`S126SdkLinkedCurrentV1.owned_stage1_source_linked_first` and
`borrowed_stage1_source_linked_first` install the actual source decoder and
candidate encoder in that same enclosing reference execution. Their
`SourceLinkedFirst` conclusion exposes the **same actual decoder statement**,
its common afterstate and actual encoder candidate, the original proof
Vec/suffix/gate and the current `firstCurrent` call. The existing checked S6
reuse theorem transports the already derived decoder success; no second parse
or independent `firstCurrent` success is assumed. The borrowed version
consumes the complete borrowed/owned equality, including reverse release.
These are ACCEPTED-ONLY reference caller theorems, not TOTAL native execution
or a concrete installation of every remaining verifier Ops slot.

Focused local `lake env lean -j1 -M4400` receipts, serialized under the atomic
local lock, are `s2-sdk-linked-caller-v2` (exit0,27.707706958s,
3174350848B RSS,swap0) and `s126-sdk-linked-current-v2`
(exit0,20.599522041s,3195207680B RSS,swap0). Both files print two axiom
reports containing only propext/Classical.choice/Quot.sound. Failed v1
elaborations are retained and excluded. Exact source/tool/direct-import and
selected transitive import pins accompany the successful receipts; no
unchanged full manifest replay ran.

There is also a narrower native result, separately accepted as
`sdk-native-entry-cut-v2`: all2515 non-cover properties pass and all3 covers
are reached (raw CBMC exit10,52.224s,2152704KiB RSS,swap0). Across arbitrary
unseeded buffer bytes, independent data/lamport slot maps, metadata, signed
borrow counters and all nonzero Rc headers, reaching the actual688-byte
proof-prefix comparison derives canonical data slots. Only688-byte memcmp
calls are marked and forced to return1; other lengths use the original libc
model. The native body/helper prefix remains unchanged. This is a
**pre-comparison entry** result, not original comparison equivalence or
first/verifier-entry linkage. One inherited cover caption mentions verifier
entry; its checked predicate is actually the pre-comparison marker. The
source-only `sdk-native-entry-audit-v1` (exit0,0.270s,48028KiB RSS,swap0)
checks the nonzero tagged marker's actual unsigned-long type/initializer,
exact C cut and replacement-before-append ordering. It prevents attributing
the cut to a recursively replaced comparison or a zero-initialized ghost.

The stronger native first-entry link and shared-allocation frame have **not**
been proved. All heavy attempts had fresh admission, High6G/Max8G/Swap0:

| Attempt | Unclosed check | Exit | Wall seconds | RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| sdk-shared-prefix-check-v2 | DFCC shared native/borrowed prefix frame |1|189.095|374116|0|
| sdk-shared-prefix-check-v3 | Reachability cuts beyond decoder; solver timeout |1|208.480|6390144|0|
| sdk-shared-prefix-check-v4 | Exact arbitrary Vec construction; solver timeout |1|206.314|6389772|0|
| sdk-shared-prefix-check-v5 | Canonical data-slot focused frame; solver timeout |1|204.687|6390068|0|
| sdk-native-context-check-v16 | All-alias native first-entry normalization |1|183.480|6391780|0|
| sdk-native-entry-cut-v3 | Arbitrary comparison reply and first-entry link |1|243.262|see correction|0|

The v3 entry-cut timeout handler lacked `import os`, so it raised NameError
before killing CBMC. Its historical runner receipt's122944KiB peak excludes
the orphan and **must not be reported as the solver peak**. The retained
cgroup peak is6594756608B; the orphan was observed at6444080KiB RSS. After
verifying PID1722041/PGID1722041 and its exact ready-program command, it was
killed and absence confirmed. `voluntary-stop.json` records this correction.
The driver now imports os; the failed run is excluded and has not been rerun
unchanged or with a higher cap. Source-only failed sources/commands/receipts
and small logs or large-log hashes are retained, along with the pinned Kani
arbitrary-Vec constructor source. No frame or first-link claim follows from
any timeout.

The packet checker now selects71 current Lean targets and22 SDK cuts. Those
counts describe evidence selection, not component closure. S2 still needs the
general actual SDK/native-to-reference state/heap connection, concrete child
installation and complete errors/log/state/ordered-oracle transport. The
native context still has fixed rooted buffer lengths and common successful
typed child hooks and a pure scan abstraction. The richer reference witness
removes the independent decoder/encoder/gate/current-first matching premises
at that reference boundary; it does not discharge those native premises.
S6 retains actual caller/runtime installation and S1 retains original
Prepared::new/prepared_claim preparation/trace/caller correspondence and the
S4 adoption re-pin consequences. The b2727acd component freeze remains
explicit; no production source changed. The raw100-bit per-attempt target
remains **not yet established**. The next native proof should split state and
loop steps rather than replay any unchanged whole-stage solver attempt.

### 2026-10-22 — input-construction experiment excluded; no native upgrade

The successful shared reference caller witness above is committed/pushed at
`aec76bb39`. Follow-up native experiments changed **harness input allocation
only**, leaving the frozen adapter body intact. Fresh byte allocations are
filled in place using a linked CBMC byte-havoc intrinsic before Rust
`assume_init`; no zero/prefix/tag constraint was introduced. The intrinsic's
primary source declaration is URL/hash pinned in
`cbmc-input-constructor-source-pin.json`. It is additional explicit tool
semantics, not source correspondence evidence.

The first version (`sdk-native-context-v15`,
`sdk-native-entry-cut-v4`) fails Kani's reachable unsupported-foreign-call
check. Every cover is unreached; raw exit10 here is **failure**, not the
successful reached-cover exit10 interpretation of v2. Its19.745s,
1420364KiB RSS,swap0 receipt and failed property projection are retained and
excluded. The successor replaces a compiled Rust harness initializer call
with the exact linked C implementation, avoiding that unsupported boundary;
no adapter function is replaced by the initializer.

That successor (`sdk-native-context-v16`,
`sdk-native-entry-cut-v5`) still times out (exit1,185.879s,
6392520KiB RSS,swap0). The same construction applied to the smaller full
native/borrowed decoder-entry frame (`sdk-shared-prefix-v6`,
`sdk-shared-prefix-check-v6`) also times out (exit1,208.489s,
6390024KiB RSS,swap0). Their corresponding optimized codegens19/20 and
shared6 succeed, but codegen is not proof. All scopes had fresh admission,
High6G/Max8G/Swap0, and the existing180s per-stage deadline. Both timeout
handlers now kill their solver groups correctly; subsequent process-table
inspection confirms no matching orphan. Exact failed source/tool/command/
resource evidence and the cleanup record are retained; none is accepted.

This experiment does not establish that large input-array copies alone cause
the resource problem: removing those copies did not make either check pass.
Do not repeat these unchanged or raise their caps. The next decomposition
needs to isolate the particular SDK transition/frame relation that grows,
then compose it with the existing primitive borrow and parser results.
The accepted native result remains pre-comparison v2; no first-entry, new
native frame, actual whole-SDK, TOTAL or S1/S2/S6 closure is claimed.
Read-only research reinspection at380b084451eaede1bb03fd0f4da7e692367a8de9
is recorded separately: the aggregate freeze decision remains b2727acd,
with the previously recorded S4 adoption changes requiring re-pinning.

### 2026-10-22 — actual SDK method contracts pass; caller composition still open

S2 is **OPEN**. No enclosing native caller premise was removed by this batch.
The reference caller theorem at `aec76bb39` remains ACCEPTED-ONLY; it does not
identify its heap with an arbitrary actual SDK execution. S6 and S1 consequently
retain that caller connection, in addition to their previously listed residuals.

The new source-only `sdk-live-contracts` packet checks the actual
`solana-account-info=2.3.0` bodies of `try_data_len`, `try_borrow_data` and
`try_borrow_mut_data`. Isolated SDK copies add proof annotations only. Removing
the recorded annotation restores the original lib.rs SHA256
`6b59aba664bb70fda6e17bcc8cf6eb41fc0bc9d8bcbb797bd70c1b107809c29a`.
No SDK or production source body changed. The method contracts cover exact
success/AccountBorrowFailed status, signed borrow-counter transitions, the
counter-only write frame, and (for live guards) their complete two-word host
representation. The harness drops the actual guards and checks restoration.
It includes all byte values and lengths0..10MiB, every signed data/lamport
counter, nonzero usize Rc headers, and all metadata on its one-account fixture.
This is a bounded host-ABI source-helper check, not unrestricted Lean TOTAL,
general runtime heap embedding, SBF ABI correspondence, or whole SDK closure.

| Actual method contract | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| sdk-live-length-join-v1 |0|32.672|3029240|0|
| sdk-live-shared-join-v1 |0|15.336|1496880|0|
| sdk-live-exclusive-join-v1 |0|15.245|1496440|0|

All776/763/763 non-cover checks pass and each has3 reached covers. No stubs
are used. Separate source/property metadata audits pin the actual contracted
SDK function, write frame, generated artifacts by hash, lock, tools and proof
receipts. `#print axioms` is N/A for these Rust/Kani checks. Exact sources and
receipts govern target provenance: the host receipt's inherited
`source_revision=d8fc9db...` is bookkeeping, not a claim that this tree was
compiled from that Git commit. All heavy scopes had fresh admission and
MemoryHigh6G/MemoryMax8G/MemorySwapMax0; inspection scopes used1G/2G/0.

Direct verified-stub composition is **not proved**. v7 codegen rejected missing
local method proof registrations; v8 registered all three but Kani then required
`Arbitrary` instances for `Ref`, `RefMut` and `ProgramError` return types that
are unavailable. No restricted or fabricated Arbitrary instance was installed.
Real-guard model alternatives are explicitly UNPROVED and excluded: the paired
shared v1/v2/v3 checks were stopped at199.161/146.603/244.595 seconds, with
6553044/6571092/6563904KiB peaks. Reducing storage to64bytes in v3 did not
resolve the problem. Length model v1 was stopped at338.760s/6582548KiB;
v2 timed out at604.724s/6637068KiB. Replacing derived error equality with
constructor matches was insufficient. The native/reference prefix v10 also
timed out at211.925s/6529868KiB. All have swap0 and terminal failed receipts;
none supplies equivalence, a frame certificate, or evidence of a counterexample.

The alias inspection was stopped without returning value-set results
(exit15,360.245s,1118556KiB,swap0). A successful function inventory establishes
only that unused shared/exclusive model bodies and derived ProgramError
equality were absent from the length-v2 program. It does not identify the
solver's root cause. Pointer provenance, inactive String-drop glue and fixture
destruction remain hypotheses, not diagnoses. No unchanged retries or higher
caps are justified by these results.

The next decomposition isolates the unchanged **native-only decoder-prefix
frame**, without loading or executing the second owned-reference program.
The same arbitrary native SDK fixture, decoder-error cut and permitted counter/
hit writes remain. This separates the concrete write-frame obligation from
paired-program composition; codegen alone does not establish it. If it passes,
the actual scan transport, success continuations, concrete child installation,
general runtime heap and ordered error/state/log/oracle join still remain.
If source fission is needed, it must be an isolated candidate preserving actual
SDK guards and errors, with explicit equivalence and re-pin gates; no such
candidate is adopted here. The frozen component target remains b2727acd and
the raw100-bit per-attempt target remains **not yet established**.

Follow-up native-only checks are terminal and excluded. Removing the entire
owned-reference execution did not make DFCC pass: native-prefix-frame-v1 timed
out (exit1,193.726s,6543220KiB,swap0). The next version removes DFCC entirely,
chooses one unconstrained root/index, and checks that original byte and all
Vec addresses/lengths/capacities after the unchanged native decoder-error
prefix. This is a different pointwise proof obligation, not an assumed frame
or restricted byte fixture. It too timed out (native-point-frame-v1,
exit1,183.295s,4429492KiB,swap0). Thus the second execution and per-byte DFCC
instrumentation are not individually sufficient explanations for the timeout.
There is no new native byte-frame theorem, extensional composition theorem,
or enclosing premise removal. Both deadlines killed their solver groups;
subsequent process inspection found no matching solver. The unchanged native
source is retained at sdk-shared-prefix-v11/v12, together with their codegen,
admission, raw pipeline, timeout and terminal resource receipts. Neither
unchanged job should be repeated or run with a higher cap.

Read-only source inspection at research0c2c0722f23103f30f25c0cf66169795dcdebc66
confirms that program lib.rs, adapter and verifier.rs remain byte-identical to
their b2727acd versions. This is recorded in
`sdk-live-source-freeze-20261022.json`; it does not establish equality of all
dependencies or release artifacts and does not supersede the freeze authority.
The focused packet checker accepts only the three actual-method contracts.
No Lean source changed and no unchanged Lean/full manifest replay was run.

### 2026-10-22 — separate common-spec checks; transport not yet established

The next model check avoids executing native and reference consecutively.
Each reference independently satisfies the **identical actual SDK method
postcondition**, with only the parameter renamed from self to account. Its
input is still actual AccountInfo and its output is still actual std Ref or
RefMut; no shadow guard/account type or fabricated Arbitrary instance is used.
Both postconditions include the counter-only write frame and complete two-word
host guard representation. The model harness also checks actual guard Drop
and unchanged scalar/header fields on the same explicit finite heap domain.

The original free-function model contracts pass (length/shared/exclusive:
9.149/8.869/8.720s,439024/444132/443360KiB,swap0). However, using those free
functions as SDK method stubs fails codegen due to the SDK impl's early-bound
lifetime parameter. An associated-function namespace fixes that signature
without constructing a new value or replacing any SDK carrier. The complete
associated model checks also pass, independently, without stubs:

| Unary associated-model contract | Checks/covers | Exit | Wall s | RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| sdk-live-model-contract-length-join-v2 |741/3|0|8.188|439992|0|
| sdk-live-model-contract-shared-join-v2 |763/3|0|9.814|444064|0|
| sdk-live-model-contract-exclusive-join-v2 |760/3|0|10.230|445228|0|

These do **not** establish method equivalence by themselves. Before ordinary
stubs can receive correspondence credit, the common specification must be
proved functional and complete for caller-observable outcomes and state on
the pinned ABI, including pointer representation, live guard use/drop and
allocation/log/oracle behaviour. General runtime-to-fixture embedding remains
separate. All failed paired model certificates remain excluded. No enclosing
source/caller premise has been removed in this batch; no native S2 closure,
S6/S1 closure, unrestricted TOTAL or100-bit claim is made.

Metadata restoration exposed a cache hazard: length-v1 codegen-v2 exited0
without replacing the shared package's most recent exclusive metadata. Its
target-kind check correctly rejected the stale metadata. That codegen is not
an accepted proof/artifact restoration. v2 gives each model crate a unique
package name and snapshots its matching method metadata/program hash directly
after the successful check. Original SDK method metadata had already been
snapshotted in their original audits; those checks remain unchanged. Source,
lock, flags, tool, source-contract and matching target pins are retained.

The last native pointwise timeout log reached SAT checks and then built error
traces. CBMC6.8.0's pinned option source shows that JSON UI implicitly enables
traces outside cover mode. A focused run of the **identical compiled target**
with only the output format changed still times out (plain-v1,
exit1,180.180s,4455248KiB,swap0), now after two SAT checks and during the next
propositional reduction. Therefore trace generation alone is not a sufficient
explanation. No failed property or reached cover is inferred from those SAT
messages without the complete report. The associated-model native pointwise
candidate also times out (exit1,183.192s,4762264KiB,swap0); it is excluded both
for timeout and for the still-unproved ordinary-stub transport. Codegen success
is not correspondence. All heavy scopes retain fresh admission and6G/8G/0.

A property inventory identifies2311 properties in the original SDK v12
pointwise program. The next partition checks only the named byte-preservation
assertion; every other safety/unwinding/caller property remains unproved by
that partition and a complete checked union is required before any whole-frame
claim. This is an explicit proof partition, not an assertion that dropped
properties pass. No unchanged all-properties replay or higher cap is planned.
That first named-property partition also timed out (exit1,180.163s,
3989580KiB,swap0). It supplies no byte-frame result, even in isolation. Its
terminal receipt and timeout are retained; no solver from these jobs remains
live. A further decomposition must change the byte-frame proof representation
or establish the complete common-spec method transport, rather than repeat
these unchanged native jobs. The priority and closure criteria remain S2 first.

### 2026-10-22 — complete native decoder-prefix observation partitions

**S2 remains OPEN; no enclosing successful native caller premise has been
removed.** The original-SDK decoder-error prefix now has a complete checked
partition of its original buffer observations. This supersedes the earlier
statement that no native byte-frame result exists, at precisely this bounded
prefix scope. It does not establish successful stage1 correspondence.

The new source-only packet is
`evidence/s126-current-caller-20261021/sdk-native-frame-windows/manifest.json`.
The focused checker is `tools/s126-sdk-modular-20261021/check-native-frame-packet.py`.
It verifies every manifest hash, exact enabled property inventory, source/body
pins, unchanged arbitrary native inputs, and that partitions differ only in
the ghost root/index. Original SDK methods are executed without replacement
stubs. Every buffer byte is arbitrary; data and lamport aliases remain
independent, as do all signed borrow counters and nonzero usize Rc headers.
The original full 58295/1880/1768-byte allocations and Vec descriptors are
retained. Instruction/account lengths remain 0..3.

Public/root1 and checkpoint/root2 all-properties checks pass every 1969
noncover property and reach both covers. Proof/root0 is split into fifteen
aligned 4096-byte observation windows, truncating the last at 58295. Window0
passes 1970 noncovers; windows1..14 pass 1971 each; every case reaches both
covers. Differences in counts arise from the ghost-window scalar checks.
These are complete enabled inventories, not selected byte-only checks. Raw
CBMC exit10 denotes the two reached covers; the checker rejects any other
failed, missing, duplicate or unchecked property. Exact per-target wall time,
RSS and zero-swap receipts are retained. Window solver time ranges73.982 to
177.923s (window0 137.223s); maximum RSS2917116KiB. Root1/root2 use
23.465/22.600s and1033628/1040712KiB. All solvers have fresh admission,
MemoryHigh6G/MemoryMax8G/MemorySwapMax0. Two sequential queues never reserve
more than16G for these solvers. Metadata audits have1G/2G/0 scopes.

`S2SdkNativeFrameCoverageV1.lean` proves `index_covered`,
`proof_buffer_frame`, `bounded_buffer_frame`, and `all_buffers_frame` by
division/remainder and list extensionality, without concrete byte reduction.
Every proof index is representable by the exact u16/4096 window observer.
The smallest changed target passes on Lean4.32.0 with-j1-M4400 in0.669s,
804072KiB RSS, zero swaps; all four axiom reports are[propext,Quot.sound].
Bundled Init/Omega import and tool hashes are in the Lean audit overlay;
source SHA20a9919c3f57b884d830d6c76ee4ac1728be998c5ba7d0ac68504f7d90a742b8.
The unknown local Lean lock was retained. No cold dependency build or unchanged
full replay ran. The initial coverage attempt failed due to multiplication
order (0.838s,816240KiB); its error-recovery sorryAx report is excluded, and
its exact failed source is retained. There is no sorry in the accepted source.

The first plain-output renderer omitted IDs containing Rust bracket types
and multiline descriptions. The complete raw solver logs were retained.
`audit-native-root-frame-host.py` reconstructs exact IDs against each enabled
inventory, retaining the old incomplete renderer separately. Corrected
`properties-complete-v2.json` and `property-audit-v2.json` establish complete
coverage. This was a reporting defect; no solver success was inferred from
the incomplete reports and no unchanged solver replay was needed.

An additional native-only `sdk-native-entry-facts-v1` check derives admission
facts from decoder entry: exact instruction length/selector/split, three
accounts and pairwise-distinct keys, proof/public readonly nonsigner flags,
checkpoint ownership/writable flags, original public/checkpoint allocation
identity, and shared/exclusive borrow-counter admission. It passes all1889
noncovers and reaches both covers (24.970s,918208KiB,swap0), with the exact
decoder-cut InvalidAccountData result. No owned reference runs in that check.
Its complete inventory/report is independently checked by the focused packet
checker. It does not derive checkpoint zero bytes from an abstract scan result.

The unrestricted root0 observation still timed out (183.944s,4020356KiB), and
executing the native plus complete reference on the same original buffers
without DFCC still timed out (187.124s,6504020KiB). Both are excluded, preserved
and not rerun unchanged or with higher caps. Successful partition checks do
not promote either timeout into a paired source correspondence proof.

**Remaining premises and next concrete deliverable:** native decoder-entry
facts plus the independently checked byte frames must construct the emitted
reference admission state, using actual std-any/source-scan transport.
The source/cut transport must justify replacing the decoder-error observation
with the actual installed decoder and successful continuation. Then the
actual successful native stage1 must join the existing installed
`borrowed_stage1_source_linked_first` theorem, preserving child errors, guard
lifetimes, checkpoint effects, release observer None and ordered oracle trace.
General runtime/host-ABI embedding remains explicit. These are implementation
obligations, not cryptographic assumptions; the new coverage theorem does not
hide or discharge them by packaging them as a record. S1 original Prepared
correspondence and S6 actual-caller binding remain open behind this connection.
No TOTAL, full S2/S6/S1, or raw100-bit conclusion follows from this packet.

The authority remains the b2727acd freeze; no shipped source changed. Exact
candidate source hashes and de1e75322 context are authoritative for these new
uncommitted checks. Historical capped receipt source_revision d8fc9db is host
bookkeeping, not a new freeze or a claim that these candidates exist at that
revision. Lean's log-derived audit overlay supersedes the generic raw receipt's
inapplicable N/A axiom field. Aggregate adoption/re-pin and final coherent
release dependency replay remain required before a release claim.

### 2026-10-22 — initial-account identity now derived by the complete reference

The latest lead handoff was read at f4669da3e, including its fourteen
`S2CallerFacts` fields and the distinction between initial native snapshots,
the full58295-byte proof account, its57607-byte suffix, ASQ8/ASF8 and the two
checkpoint carriers. The next checked deliverable directly addresses its
existential-input concern. See `S126-FIXED-INPUT-HANDOFF-20261022.md` for full
statements, before/after audit, exact remaining boundaries and receipt table.

`S2SdkFixedInputCallerV1` derives two extra conclusions from the SAME complete
installed reference stage1 success: its proof and public byte views are the
literal account0/account1 reads from the FIXED initial SDK heap. No independent
byte/frame/clone/child/prefix/tag premise is added. `S126SdkFixedInputCurrentV1`
retains these equations while composing the actual source decoder, common
statement candidate encoder, original Vec range/gate and current first wrapper.
`S126SdkFixedInputExportV1.borrowed_stage1_fixed_input_witness` additionally
exports exact proof-account length58295, suffix contents drop688/take57607,
suffix length57607 and actual decode/current-first calls for the same bytes.
`forget_initial_inputs` kernel-checks that this strengthens the PREVIOUS exact
source-linked predicate, with its original quantifiers/carriers/results.

Focused targets pass in14.591/6.007/17.925s, maximum RSS3492069376bytes,
zero swaps and nine standard-only axiom reports across the accepted three
targets. Their5614 selected import hashes are recorded without exporting
objects. The changed generic/source-walk target was checked first, then its
current-first bridge and suffix export. There was no unchanged full replay.
The explicit ignored fields remain actual syscall/digest/verifier-child
interpretation; this is accepted-only reference success, not arbitrary-child
TOTAL or native/runtime identity. Initial owned SDK views are not silently
equated with the lead's externally fixed native stored/public snapshots.

Separately, the native-derived entry scalar facts construct the complete
borrowed-reference decoder-error prefix in `sdk-reference-admission`:
all1722 checks and both covers pass, exit0,15.182s,575428KiB RSS,swap0 under
fresh6G/8G/0 admission. This avoids the timed-out two-execution solver target.
It preserves arbitrary bytes and metadata, independent lamport aliases and
arbitrary proof slot; pointer and scalar restoration are conclusions. Same
scan result, original-buffer/native embedding and successful continuation
substitution remain explicit. The borrowed parent equals the previously
checked source; local-path snapshots recorded after the check are not a new
freeze. Both focused evidence checkers pass without solver/Lean replay.

S2, S6 and S1 remain OPEN. The next enclosing obligation is actual successful
native SDK-to-fixed-initial-reference correspondence, with installed children
and their ordered effects. Native decoder-error frames do not prove it.
TX2 reconstruction/retention, remaining lead interface fields, original
Prepared/prepared_claim trace correspondence, full R22 and release re-pin/
coherent replay remain required. No shipped source or release artifact changed.

## 2026-10-22 successful-entry and checkpoint-writer progress

The latest exact handoff is `S126-FIXED-INPUT-HANDOFF-20261022.md`.
All17 corrected original-SDK first-entry coordinate gates are checked and
source-only audited, extending the older decoder-error-prefix scope. The
complete borrowed-reference success constructor is also checked under the
stated native-derived facts and child/gate/scan conditions. These do not yet
instantiate the actual runtime/caller/source/oracle join.

At the extracted reference layer, the complete installed caller now derives
fixed initial proof/public views, actual decode/current-first, exact compact
suffix and SAME returned checkpoint saved at the original account2 slot
after full release (`CheckpointWriter.borrowed_stage1_fixed_saved_current`).
No independent writer/child/range/frame premise is added. Physical native
storage, account metadata, cross-transaction checkpoint/TX2 public transport,
actual child installation and ordered oracle correspondence remain. The lead's
fourteen-field `S2CallerFacts` is still not populated in full; no cone closure.
