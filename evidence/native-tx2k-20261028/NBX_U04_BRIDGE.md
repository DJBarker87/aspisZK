# NBX U04 — ruling (s) native instances

Status: OPEN. The historical NBU “not a soundness obligation” classification
is superseded by ruling (s). Retain all inherited NBU/NBN results without
re-proving them. Each op15, op23, op25–34, op48/op49 requires representability,
frame and SAME-argument call-site association for one real native instantiation.
No body-fidelity or adapter-law premise is introduced.

Slot inventory correction: op31 = V1 registry, op32 = V1 entry,
op33 = V2 registry, op34 = V2 entry, per coherent AdapterRw.Ops.
Digest/error remain op43/op44.

Frozen Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
The source and inherited ELF pins are unchanged. This is no release claim.

## Stage 2: candidate value selection and local native frames

NBX_SlotValues uses the original AdapterRw carrier and updates only the
existing op15/op25–30 fields. op15 reuses PoolS2_PolicySource unchanged.
The six getter functions have full typed domains (no validity/canonicality
precondition), exactly one explicit record, plus current_slot for op29/op30.
The candidates add no adapter-law hypothesis. The selection/continuation
lemmas are local SDK composition, not the whole headline extraction theorem.

NBX_SOURCE_ASSOCIATION.json records every native occurrence in frozen
r1_pool_adapter.rs and its owned boundary alongside the corresponding emitted
SDK call. op15 receives master.verifier_policy; op25–28 receive the same decoded
registry; op29/op30 receive the same decoded entry and current_slot. This file
is a source inspection artifact, not a proof of the enclosing caller.

K003–014: actual getters on arbitrary complete records and arbitrary slot,
with arbitrary-coordinate input and ambient frames. Each positive has its
matching failing inverted assertion under identical KMX/frozen configuration.
K015–022 additionally check both retirement getters, status decoding and
required_binding_is_zero. These are local native evidence, not whole U04 closure.

Additional attribution correction: op15 itself is only
validate_verifier_policy_v1(&master.verifier_policy). Identity and policy byte
decoders are reached below op48/decode_master_box, not standalone op15 calls.
op48/op49 include the actual Box allocation and ProgramError mapping; a pure
inner struct decoder does not by itself close that wrapper's instance.

Validation stage2: NBX_L002 compiled NBX_SlotValues with exit0,
5.180256306s, peakRSS5,375,668KiB, swaps0. All nine printed roots use no axioms
or only propext/Classical.choice/Quot.sound. L001 is rejected, not evidence.
K003–022 establish ten positive/failing-control pairs; K001/K002 were own
compilation-input failures and are excluded. Exact sources, commands, frozen
graph, lock pre/post hashes, dependency/tool pins and cgroups are in per-attempt
receipts and NBX_ATTEMPTS.jsonl. No native whole extraction is claimed.

## Stage 3: decoder and loop components

K023/024,025/026,027/028,029/030 cover op31/32/33/34 respectively on
arbitrary full wire images of 128/192/256/320 bytes. Two invocations receive
the SAME slice; the complete Result is compared (success record or exact error),
and an arbitrary input byte is framed. Controls invert the same conjunction.
There is no canonical/valid header precondition. These gates establish local
exact-width determinism and input frame; they do not supply a native result
model, arbitrary-slice admission, external heap frame or complete extraction.

NBX_FrameComposition.scan_value proves reserved scanning by list induction.
rows_value and rows_ext prove source-ordered reads use the same original reader.
NBX_RowFrames is the corresponding intended in-place value/frame induction,
to be checked after the native batch, one capped scope at a time.
Native master/checkpoint cuts execute exactly one row update with an arbitrary
pre-state, lane and observation coordinate. No full sequence-loop replay,
whole-buffer decoder loop, field multiplication or SHA is attempted.

L003 (NBX_FrameComposition) exit0,5.709678515s,peakRSS5,419,532KiB,swap0;
all four printed roots use only standard axioms or none. The return-data law
is an obstruction lemma; it does not assert a successful ASR8 encoder.

## Per-slot extraction ledger (no body-fidelity substitution)

No row below is marked whole-instance CLOSED. In particular, SDK selection is
not silently promoted to the headline's AeneasExtraction premise.

| Slot | Native function / passed arguments | Current component; remaining obligation |
|---|---|---|
| op15 | validate_verifier_policy_v1(master.verifier_policy) | selected unchanged PoolS2 source; full typed native frame/determinism pair. OPEN actual caller extraction/carrier composition. |
| op23 | decode_pool_v1_pair_forest_terminal_request_v1(instruction suffix) | arbitrary exact-width wrong-magic rejection and original payment-window frame. OPEN success branches, lower child argument/frame and native caller composition. |
| op25 | VerifierRegistryV1::is_paused(registry) | native arbitrary-record value/frame + Lean selected/continuation. OPEN actual enclosing native caller extraction component. |
| op26 | VerifierRegistryV1::is_immutable(registry) | same full-domain component as op25; OPEN actual enclosing native caller extraction component. |
| op27 | VerifierRegistryV2::is_paused(registry) | same full-domain component; OPEN actual enclosing native caller extraction component. |
| op28 | VerifierRegistryV2::is_immutable(registry) | same full-domain component; OPEN actual enclosing native caller extraction component. |
| op29 | VerifierRegistryEntryV2::is_active_at(entry,current_slot) | arbitrary entry/slot, exact Bool and frame; Lean selected/continuation. OPEN actual enclosing native caller extraction component. |
| op30 | VerifierRegistryEntryV1::is_active_at(entry,current_slot) | same full-domain component; OPEN actual enclosing native caller extraction component. |
| op31 | decode_verifier_registry_v1(registry_account.data()?) | exact-width whole-Result determinism/input frame. OPEN arbitrary-slice/native wrapper/caller extraction component. |
| op32 | decode_verifier_registry_entry_v1(entry_account.data()?) | same exact-width component; OPEN arbitrary-slice/native wrapper/caller extraction component. |
| op33 | decode_verifier_registry_v2(registry_account.data()?) | same exact-width component; OPEN arbitrary-slice/native wrapper/caller extraction component. |
| op34 | decode_verifier_registry_entry_v2(entry_account.data()?) | same exact-width component; OPEN arbitrary-slice/native wrapper/caller extraction component. |
| op48 | decode_master_box(original master bytes) | identity/policy frames, one native sequence-store iteration and Lean frame induction. OPEN native Box/allocator/error frame, complete original-reader composition and caller association. |
| op49 | decode_checkpoint_box(original checkpoint bytes) | one native bounded-sequence iteration and Lean frame induction. OPEN canonical digest/Box/allocator/error frame, complete original-reader composition and caller association. |

Each remaining row needs native caller/argument/heap evidence (Kani/P6), not a
new abstract law restricting missing. The imported NBN callback-unconstrained
lemmas do not provide that evidence. op53's effect obstruction is separately
recorded in NBX_OP53_FINDING.md. No headline/security/runtime assumption changes.

Stage3 completed: all23 NBX positive/control pairs K003–048 behave as
expected; K049 additionally verifies empty-slice WrongLength from all seven
actual decoder entry points (an unpaired diagnostic, not native closure credit or arbitrary-length
closure). No solver timeout, memory kill, unwinding failure or cap increase.
K031/032 policy validator, K033–036 identity/policy decoders, K037/038 ASQ8
wrong-magic frame, K039/040 master store, K041/042 checkpoint store,
K043/044 reserved scan step, K045/046 request window, K047/048 master identity
window. The window observations select arbitrary offsets in the SAME input.

NBX_L004 compiled NBX_RowFrames: exit0,5.513528492s,peakRSS5,382,416KiB,
swap0. value_frame/read_ext prove all in-interval writes and every outside
row from an arbitrary initial state, by induction; no concrete array replay.
nonempty_return_write proves the precise return-data effect obstruction.
All printed axioms are standard. The aggregate installed-selection candidate
is still pending missing unchanged imports and receives no proof credit yet.

## Checked actual headline path

The previously inspection-only installed projection is now kernel checked.
NBX_HeadlineSelection.nativeMissing updates ONLY the existing seven op15/op25–30
fields of ONE IDa_Deployed.Uninstalled record. seed_instance identifies its
actual IDa seed with the same existing Configuration update. selected proves
all seven candidate functions survive IDa.deployedConfiguration and the outer
FIp installation. NBX_SeedAdapter.adapter proves the loaded seed's adapter is
exactly missing.adapter; the printed definition matches the frozen cohort
source. No law or additional dictionary carrier is introduced.

NBX_HeadlineRetention.op23/op31/op32/op33/op34/op48/op49/op53 prove the exact
same missing fields survive that actual headline path. Each consumes its named
NBX_InstalledOpN.retained theorem, the seed identity and the small adapter closed
form. This does NOT exhibit real native functions for those remaining slots or
discharge their native caller/frame components. Their OPEN ledger is unchanged.

L109 (headline selected/seed/remaining-adapter): exit0,4.815092277s,
peakRSS5,586,868KiB,swaps0. L111 (seed projection plus printed definition):
exit0,5.166297626s,peakRSS5,582,440KiB,swaps0. L112 (all eight actual headline
retention equations): exit0,5.410560397s,peakRSS5,583,944KiB,swaps0. Every new root
uses only propext/Classical.choice/Quot.sound. L110 is rejected simplification
failure; the named seed projection fixes it. All exact sources/import object
pins/commands/cgroups/axioms are retained, including rejected attempts.

Private missing-dependency bootstrap is not new soundness credit:87 accepted
single-module builds reuse unchanged existing sources; generated wrapper/fallback
modules recovered from retained cohort/closed-leaf sources change only import
spellings, with byte-identical non-import bodies (NBX_IMPORT_NORMALIZATION.json).
No coherent/shared source or object is rewritten. New NBX proofs retain default
heartbeat/depth options. Rejected normalization shapes L073/L075/L076 are replaced
by NBX_AdapterShape.adapter and NBX_SdkRetention plus existing NBK lemmas, not by
larger resource limits. L076 admission refused once and waited180s before a fresh
exit0/allowed:true receipt; no prover launched on the refusal.

## Remaining Lean-only loop components completed

NBX_PredicateScan.value/step generalize the short-circuit fold to arbitrary pure
predicates; byte reuses the already checked byte-scan value law, and capacity
composes the SAME original sequence reader with the u64>2^20 predicate.
NBX_SequenceDomains.within/disjoint and master/checkpoint/checkpoint_input derive
all eight-byte read ranges and separation from the actual count8 and guarded
384/192-byte input shapes. Checkpoint reads end at176 before its reserved suffix.
No concrete sequence or whole-buffer computation is unfolded.

L115 rejected an Aeneas scalar-literal simplification/transparency encoding;
L117 rejected a Boolean base-case rfl. The replacement uses a direct generic
Boolean fold and explicit two-case base proof, with no resource option change.
L118 passes the predicate module; L116 passes the domain module. Native iterator,
Box/allocator and original-caller association still require new native evidence.

Final combined audit L119 (source closure changed since provisional L114):
exit0,4.501810613s,peakRSS5,578,644KiB,swap0,revision ca1dedc93e plus recorded
exact dirty source hash. All51 new theorem roots use a subset of
propext/Classical.choice/Quot.sound. NBN_Audit and NBU_Audit are imported,
not re-proved. This is a focused audit, not a full release manifest replay.

## Disk-full continuation: returned sequence composition

NBX_SequenceResult.returned proves that observing exactly the assigned rows
of writeRows gives sequenceRows of the SAME original reader, independently
of the arbitrary initial accumulator. argument_frame permits distinct initial
accumulators and requires equality only of the passed row reads. capacity
composes the actual >2^20 scan with those returned rows. These reuse the existing
induction and scan laws; they add no native/allocator/iterator premise or credit.

NBX_L120 passes: exit0,wall4.663582181s,peakRSS5,414,860KiB,swap0;
source revision e5406c96e1 plus exact dirty source hashes. All three printed
roots use only propext/Classical.choice/Quot.sound. Admission exit0/allowed:true;
-M7000,6G/8G/swap0/tasks64. Budget now120/120 Lean and50/50 Kani.
The fourteen whole-instance rows above remain OPEN for their listed native
caller/argument/heap obligations. No remaining budget authorizes another run.
