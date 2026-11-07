# LIB0: field map for the shared RSL instantiation job

Target not yet established. This is a mapping. It closes no row, discharges no premise and proves no Lean theorem. It gives the shared instantiation job (LIB, ruling (bp)(2)(c)) the supplier of every field it must instantiate, so that it does not rediscover them.

**Inputs.**
- The frozen specs are RSL rev2 (be66076856e): RSL_Base, RSL_Pool, RSL_Verifier and the 17 row modules in evidence/rowspec-lead-20261107.
- The top interfaces are TAS_Interfaces, TAS_Top, TAS_TopB and TAS_TopB_NNE in evidence/top-assembly-20261107.
- The authoritative ledger is evidence/ledger25-20261111/NMQ_LEDGER.json.xz (582 CLOSED, 17 OPEN, gate PASS).
- The merged-job evidence was read at research 3493d38575c: NMS_, NMX_, NMP_, NMT_, NMV_, NNC_, NNE_, NNF_, NND_ and AMN_. Their *_REMAINING.md files were read in full.
- Frozen source 4bb3b3f51e1 was read with `git show` for the findings F1 and F2.

**Machine-readable form.** LIB0_MAP.json holds one record per field: the supplying row with its status, function, owner module and every root_owners name copied from the ledger, plus the adapter, the existing installation and the flag. It also holds the transcription lemmas, the flags and the module order. LIB0_gen.py regenerates it from LIB0_fields.py and the ledger (`python3 -I LIB0_gen.py <xz -dc ledger> LIB0_MAP.json`). The generator asserts that every cited supplying row is CLOSED in ledger25.

**How deeply each field was checked.** For every cited row, the ledger status, owner module and root names were read mechanically. The root statements were read for TX1:024, 029, 064, 081, 086, 129, 134, 141, 179, 186, 331, 332 (allocation scan of all 28 roots), TX2:045, 064, 152, 153 and 211, and the certificates of TX1:024, 029 and 191. For the other rows the shape was classified with a scan of the root statements: success premises, Cut/Windows binders and existentials. Each "adapter exists" entry names a term found in the merged branch. Most of those terms are partial, and the job's own REMAINING file is quoted for each. A row that LIB starts on must be read at full statement level first, rule 3.

## 1. Summary

104 fields: PoolLib 20, DeployedIds 2, V2Lib 4, S1Lib 6, VLib 66, PreparedNew 1, and the Env/EnvRep group of the TAS `Sig` 5. `Stage1` is not a LIB field: it is `TX1_344.asStage1 VL P C`, which is defined from the OPEN row 344.

| Status | Count | Meaning |
|---|---|---|
| Definitional | 44 | A carrier choice, constructor, field read, literal or headline predicate (`Root0`). No CLOSED root is needed. Each carrier must still be the one emitted copy that its child roots use. |
| Trust row | 5 | `Env.sha256/pda/clock`, `EnvRep` and `readerHeader`. These are bound by the accepted runtime rows and NNE_/NNC_ host definitions, not by ledger roots. |
| Root, adapter exists | 20 | A CLOSED root supplies the field and a merged job has an installation term. Most of these terms are partial (see the notes). |
| Root, adapter new | 27 | A CLOSED root supplies the field and LIB must write the representation adapter. Includes `qadd`/`qmul`, which are supplied by certificate theorems (F5), and `finishInputDom` (F7). |
| Unsupplied or partial | 8 | `filled`, `accNew`, `weightsNew`, `claims`, `tx2auth` (F1); `PreparedNew` (F2, F3); `decodeReachesAlloc` (F4); `checkpoint` (F6). |

Root-supplied fields in all: 55 = 20 + 27 + 8. Every root-supplied field needs at least the generic carrier adapter, because every CLOSED root is stated over Aeneas carriers: `Slice U8`, `Std.Result` with `ok/fail/div`, emitted structs, often an Ops dictionary, and several different emitted copies (AspisR1PrefixAggregateParser, AspisR1PublicPreparation, VTop_Stages, FIo_Native, AdapterRw, NFY_*). RSL is stated over `Bytes`, `Except` and `Obs`.

## 2. Unsupplied fields and their classification

**F1. Fallible reservation (try_reserve) Err arms. Affects `VLib.filled`, `VLib.accNew`, `VLib.weightsNew`, `VLib.claims` and `V2Lib.tx2auth`. Classification: demonstrable error in RSL rev2.**

Evidence:
- `heap::filled` and `heap::uninit` return `Err(Allocation)` when `try_reserve_exact` fails (crates/aspis-core/src/r0/heap.rs:5-14).
- Their callers propagate it as a returned Err: prepare (candidate.rs:256), `Accumulator::new` (verifier.rs:93), `BatchedWeights::new` (verifier.rs:207), `resume` on the TX2:064 path (verifier.rs:428) and `claims` (r1_semantic.rs:45).
- The CLOSED roots quantify the reservation. `NKA_ClaimsRoot.claims` takes the allocator, state and reservation. The NGC/NIG filled roots take the reservation. The NKH caller clause asks for "both arms".

Consequences:
- `RSL.Env` carries only sha256, pda and clock, so a faithful law for these five fields must admit both Ok and Err(Allocation) at the same arguments and Env. Also, `impl : Args → Env → Obs` cannot be the actual function.
- The RowSpec proofs are unaffected, because a relational law admits the impl.
- The TX1 returned path (345 → 328 → 094 → 087 → filled/accNew/weightsNew, and 136 → claims) becomes nondeterministic at a fixed Env. `AMN.a1_forces_det` then makes A1 unprovable: the A1min Err arm and `NND_Tx1ReturnedValues.returned`. On TX2, `tx2auth` does the same to `NND_Tx2Values.auth_ret`.
- The rev2 header says "the only nondeterminism is the allocation-failure branch at each named allocation site". That is false for try_reserve sites.

Recommendation, for the lead to apply: add a quantified reservation reply to `RSL.Env`, in the ruling (at) shape with one reply per fallible-site occurrence. Make these five laws read it, and bind it in `Sig.EnvRep` to the headline `reservation` binder. The worse alternative is an owner ruling that a try_reserve failure is outside the obligation, which would add trust. LIB builds everything else now and keeps these five fields as named parameters until the lead rules.

**F2. Domain of `PreparedNew` at the TX1:087 call. Classification: demonstrable error in RSL rev2 (RowSpec_087 Domain is incomplete), unless the lead commissions a new TX1:179 law.**

Evidence:
- The TX1:179 root (`NHS_PreparedPacket.source`) assumes `compact_check : check_values compact = ok (Ok ())` on the 464-byte y1 slice. Its ledger domain says "LPt compact464 checked".
- Frozen prepare (candidate.rs:255-264) calls `expand_values`, which does no canonicality check (compact.rs:127-136), and never calls `check_values`. Only tx1 calls `canonical_scan`, at candidate.rs:275.
- RowSpec_087's Domain has only R1-R3.
- NMP_REMAINING reports the same gap.

Consequence: with `P.dom` copied verbatim from 179, as the RSL rule requires, RowSpec_087 is unprovable.

Recommendation: add an own-input clause R4 to RowSpec_087, "proof[7031..7495] passes check_values", discharged in RowSpec_094 from the TX1:084 canonical_scan law at SAME proof. This narrows 087 only.

**F3. Law of `PreparedNew`, and the TX1:081 domain at 094. Classification: missing child lemma (TX1:179).**

The root is the Ok arm only. It assumes `semantic_finish`, `compact_check` and `returned` are all `ok`. It is missing:
- the Err arms of `t.queries(..)?` and `prepared_claim(..)?` (verifier.rs:83 and 87);
- the `Vec::with_capacity` and `Box::new` abort arms (verifier.rs:78 and 88);
- `g` on every arm;
- the exports that 094 needs for batch_merkle: `queries[j] < 262144` and the root bindings (NLO-bf:TX1:094:TX1:081:66/67).

All of these can be proved from the same emitted body (`NGN_Emitted.prepared`), with the NHS/NFW/NHL support the root already uses. RSL_INDEX item 4 anticipated this.

**F4. `S1Lib.decodeReachesAlloc`. Classification: missing child lemma (TX1:332), not an RSL error.**

None of the 28 TX1:332 roots mentions an allocation site. Aeneas emits `Box::new` as pure, so the reached sites are visible only in source positions. NMT_ has the source-derived definition `NMT_R2_ReachLibrary.reaches` and the wrong-length lemma, but not the association to those sites. This does not block RowSpec_345 or A1, because `allocIf b` admits the returned arm for every b. It is still a gate obligation, because the field must have exactly one admissible instantiation.

**F5. `VLib.qadd` and `VLib.qmul`. Classification: supplied by a CLOSED certificate theorem, not by the named root. This is ledger hygiene; no RSL change is needed.**

The ledger roots are `NEB_ArrayRefs.qm_injective` (TX1:024) and `NFS_QueryLoopRoot.root` (TX1:029). Neither is a value law. The value laws are `NEB_QMCalls.add/multiply` on canonQ inputs, with `NEB_AdditiveFrames.qm_add` and `NEB_FieldFrames.qm_mul`. The QM31 carrier must therefore be the canonical subtype. Counted as "adapter new".

**F6. `VLib.checkpoint`. Classification: adapter plus a missing child lemma (TX1:186).**

The root assumes predecessor results (op3, op4, op7 and op12 are Ok) and allocation success (`NHS_PendingReservation.heap` is Ok). So `dom` must be the ledger's DriverEstablishedDomain at SAME proof, which 094 discharges from its own earlier calls. The Vec abort arm named in the RSL comment is not exposed by the root.

**F7. `VLib.finishInputDom`. Classification: open derivation, with possible missing child lemmas (canonicality exports of TX1:129, TX1:142 and TX1:150). Not an RSL error yet.**

The NJW and NKN clauses are prose. The canonicality clauses hc..hm concern values that are computed inside 136.

**F8. The TX1:130 mark transcription (not a field). Classification: trivial missing child lemma.**

The CLOSED packet covers obs = None only, while RowSpec_136/137 quantify obs. The frozen body is `let _=(obs,i)` (r1_semantic.rs:75-80).

Two field-level points are not flags. The RSL comments for `decodeMaster` and `decodeCheckpoint` cite TX2:218/216, which are the Box wrappers transcribed as `decodeMasterBox`/`decodeCheckpointBox`. The decoders themselves are TX2:153/152 (NJY_Roots). The comment is imprecise, but no statement is wrong. Separately, NMT_ builds its S1Lib in the copy namespace `NMT_R2.TX1_345`. LIB must target the canonical `RSL.TX1_345.S1Lib` and check equality of the two by `rfl`.

## 3. Cross-cutting adapter requirements

1. **Byte and Result carrier.** The maps are:
   - `Slice U8 → Bytes` (`List.map` of the byte embedding; injective);
   - `Array U8 32 → B32`;
   - `Std.Result (core.Result α ε) → Obs (Except ..)`, with `ok` → `ret`, `fail` → `abort` (prefix only) and `div` → `diverge`.

   NMS_R2N_Interpreted.mapObs/Simulates, NNC_ByteCarriers and NMS_R2N_RSLScalars cover pieces of this. LIB_Carriers should consolidate them once.
2. **Graph-of-model laws.** Every `Child.law` and every Spec-valued PoolLib field must be the graph of the root's deterministic model at (args, env), plus only the abort prefixes the RSL comment names. It must never be the image of a native Cut relation. Each field also exports a `Returns` evaluator (NND_Returned/AMN shape), so that the integration job can build `NND_PoolValues.Values`, `NND_Tx2Values.Values` and `NND_Tx1ReturnedValues.Values` by composition. NMS_R2PoolSites.scan/reconstruct are existential images over an injective byte map. They are functional if the underlying interpreted relation is, and LIB must prove that.
3. **Emitted-copy identification.** Each RSL carrier is one emitted copy. `PrefixAdapter.fromOld` (Prefix) and the NJS_Extract = Op3I_Source equality (TX1:086) are examples of the bridges needed. Every child root on a different copy needs its bridge.
4. **Env.** The digest children (131, 150, 134, 142, 064) render `Event.digest parts (env.sha256 parts)`. The roots take `hashv`/`Digest32` parameters, which must be instantiated from `Env.sha256`. Partial work exists in NNC_RuntimeOracle and NNC_DigestTrace.
5. **Domains.** `Child.dom` is the CLOSED child's ledger caller clause, copied verbatim (RSL_LEDGER_CLAUSES.json). Prose clauses (NJW, NKN, NKC, NKH, NKW) need a Lean transcription, recorded clause by clause. Weakening a domain is a gate finding.

## 4. Field tables

### PoolLib (20 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `Request` | - | carrier := emitted PoolV1PairForestTerminalRequestV1 of the copy used by TX2:163 roots (NFY_Part059); identify with the AdapterRw copy | none | DEF | opaque carrier; must be the TX2:163 output type |
| `Statement` | - | carrier := emitted PoolV1PairForestTerminalStatementV1 (TX2:224 output = TX2:165/219 input); one copy for all three | none | DEF |  |
| `Afterstate` | - | carrier := scan_proof_buffer candidate afterstate (TX2:226 output = TX2:224 input) | none | DEF |  |
| `decodeRequest` | TX2:163 `NFY_NFD_RequestDomains.binding_fields +22` (NFY_Part059) | Slice U8/Std.Result(Result Request DecodeErr) -> Bytes -> Option Request (byte image + Ok/Err->some/none); all lengths | NMS_ NMS_R2DecoderImage.full, NMS_R2RequestBranches (partial) | ROOT, adapter exists | NMS_REMAINING: concrete request B32 byte representation still to fix |
| `reqProfile` | - | field read; [u8;32] -> B32 adapter | NMS_ NMS_R2Gated242 (literal key guards) | DEF |  |
| `reqRelease` | - | field read; [u8;32] -> B32 adapter | NMS_ NMS_R2Gated242 | DEF |  |
| `reqPoolProgram` | - | field read; [u8;32] -> B32 adapter | NMS_ NMS_R2Gated242 | DEF |  |
| `reqNullifier` | TX2:158 `NGE_NEQ_NullifierDomains.common_independent +2` (NGE_NEQ_NullifierDomains) | native eight-word nullifier array -> B32 (32 bytes) representation | NMS_ NMS_R2NullifierCarrier.full (partial: B32 byte rep not fixed) | ROOT, adapter exists |  |
| `outputLane` | TX2:156 `NFY_NEM_LaneReached.lane_instance +1` (NFY_Part031) | B32 -> Option UInt8 from lane_instance model; nullifier byte link | NMS_ NMS_R2LaneModel.full (partial: outputLane link open) | ROOT, adapter exists |  |
| `decodeMaster` | TX2:153 `NJY_Roots.master +2` (NJY_Roots) | NJY_Master.model (Cut-indexed, functional model) -> Option RSL.Master field-by-field (PoolIdentity, VerifierPolicy, Digest=List UInt32) | none | ROOT, adapter new | RSL comment cites TX2:218 (the Box wrapper, transcribed as decodeMasterBox); the decoder itself is TX2:153. NND A2/233 lists the payload decoder as remaining |
| `decodeCheckpoint` | TX2:152 `NJY_Roots.checkpoint +2` (NJY_Roots) | NJY_Checkpoint.model -> Option RSL.Checkpoint | none | ROOT, adapter new | RSL comment cites TX2:216 (Box wrapper); decoder is TX2:152 |
| `validatePolicy` | TX2:151 `NHY_PolicyModel.actual_slot` (NHY_PolicyModel) | is_ok of NHY_PolicyModel on VerifierPolicy carrier | NND_ NND_RegistryLibrary.install / NND_PolicyValue.native | ROOT, adapter exists | NND link is to AdapterRw op15; LIB must also tie it to NHY_PolicyModel.actual_slot |
| `decodeRegistryV1` | TX2:203 `NJY_Roots.registry +2` (NJY_Roots) | Option image of NJY_Roots.registry model | NND_ NND_V1DecoderValues.registry | ROOT, adapter exists | NND link is to AdapterRw op31; tie to NJY_Roots.registry |
| `decodeRegistryV2` | TX2:204 `NHY_RegistryJoin.cohort` (NHY_RegistryJoin) | Option image of NHY_RegistryJoin.cohort | NND_ NND_V2DecoderValues.registry | ROOT, adapter exists | tie to NHY_RegistryJoin.cohort |
| `decodeEntryV1` | TX2:201 `NJY_Roots.entry +2` (NJY_Roots) | Option image of NJY_Roots.entry | NND_ NND_V1DecoderValues.entry | ROOT, adapter exists | tie to NJY_Roots.entry |
| `decodeEntryV2` | TX2:202 `NIJ_EntryJoin.cohort` (NIS_EntryJoin) | Option image of NIJ_EntryJoin.cohort | NND_ NND_V2DecoderValues.entry | ROOT, adapter exists | tie to NIJ_EntryJoin.cohort |
| `scanProof` | TX2:226 `NFY_NFJ_Comparison.completion +8` (NFY_Part060) | RS image incl. Box site; byte image of the 58295-byte buffer | NMS_ NMS_R2PoolSites.scan (+NMS_R2N_ScanSites.interpreted, scanner_extent) | ROOT, adapter exists | representation image of a fixed source model; NMS: not a physical producer certificate |
| `reconstruct` | TX2:224 `NFY_NEU_CallDomains.common_packet +7` (NFY_Part057) | RS image incl. both Box-site aborts; Authenticated carrier map | NMS_ NMS_R2PoolSites.reconstruct (+NMS_R2N_ReconstructSites.meaning) | ROOT, adapter exists |  |
| `encodeStatement` | TX2:165 `NFY_NEQ_EncoderOracle.result_state_effects +14` (NFY_Part053) | [u8;1880] by value -> Spec (Option Bytes), no allocation arm | none | ROOT, adapter new | NMS_REMAINING: fix the CLOSED 1880-array encoder law |
| `emitResult` | TX2:219 `NFY_NEY_EmitComposed.encoder_bridge +11` (NFY_Part058) | RS Unit with the returnData event (sol_set_return_data) | none | ROOT, adapter new | NMS_REMAINING: return-data child law not installed |

### DeployedIds (2 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `pool` | TX2:220 `NHJ_DeployedIds.pool_actual` (NHJ_DeployedIds) | .rodata 32-byte constant -> B32 literal | none | ROOT, adapter new | trivial; NMS_R2Gated242 already uses the frozen deployed-pool value |
| `registry` | TX2:225 `NHJ_DeployedIds.registry_actual` (NHJ_DeployedIds) | .rodata 32-byte constant -> B32 literal | none | ROOT, adapter new |  |

### V2Lib (4 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `VErr` | - | carrier := verifier::Error (8 variants); SAME copy as NMN_064 error carrier and VLib.VErr | none | DEF |  |
| `debug` | TX2:211 `NIJ_ErrorJoin.source` (NIS_ErrorJoin) | NGL_ErrorModel.label/message: Debug string of verifier::Error | NMS_ NMS_R2ErrorSource.full (partial) | ROOT, adapter exists | CLOSED law has no format! allocation; harmless: impl subset Ref because Ref admits the returned arm |
| `Root0` | - | NLP_InputDomain.Root0 on byte carriers (headline domain predicate, not a ledger row) | NNC_ WeakR0Rep.at_entry, NNC_ByteCarriers | DEF |  |
| `tx2auth` | TX2:064 `NMN_064.root` (NMN_064) | NMN_064.RowSpec Law + chronology over NLW_Full064.Frame/End -> Bytes^3 -> Spec (Except VErr Unit), abort = prefix | none | **UNSUPPLIED/PARTIAL** | F1: canonical rendering (TAS name NMN_064.rslRefines) not built; NNC_ObservedLaw.w + contains_native cover only the weak (Root0-free) library. Resume fills (verifier.rs:428) make the returned law reservation-dependent (F1) |

### S1Lib (6 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `Statement` | - | carrier := emitted terminal statement of TX1:332 (NMT Statement) | NMT_ NMT_R2_ConcreteS1.library | DEF |  |
| `decodeStatement` | TX1:332 `NFY_NEX_PublicModel.result_state_effects +27` (NFY_Part058) | 1880-byte slice decode -> Option Statement | NMT_ NMT_R2_ConcreteS1.decode (partial: total decoder transport open) | ROOT, adapter exists |  |
| `decodeReachesAlloc` | TX1:332 `NFY_NEX_PublicModel.result_state_effects +27` (NFY_Part058) | Bool: decoder reached a Box site | none | **UNSUPPLIED/PARTIAL** | F4: no TX1:332 root mentions an allocation site (all 28 are allocation-free); NMT_R2_ReachLibrary.reaches is source-derived (NMT_R2_Reach*, wrong-length lemma) without the association |
| `validateStatement` | TX1:276 `NFY_NEM_LaneReached.lane_reached +3` (NFY_Part031) | is_ok of the validator Result | NMT_ NMT_R2_PublicLibrary.valid | ROOT, adapter exists |  |
| `encodeCandidate` | TX1:278 `NGE_NEM_EncoderFrame.after_step_and_bytes +2` (NGE_NEM_EncoderFrame)<br>TX1:267 `NFY_NED_ReconstructCarriers.common_argument` (NFY_Part053) | encoder of common().lane_transition.candidate_afterstate -> Option Bytes | NMT_ NMT_R2_ConcreteS1.encode (partial: total encoder transport open) | ROOT, adapter exists |  |
| `semanticPublic` | TX1:268 `AspisR1.NJB_SemanticPublic.result` (NJB_SemanticPublic) | statement.semantic_public() -> VLib.Public | NMT_ NMT_345.semanticValue via NMT_R2_ConcreteS1.library | ROOT, adapter exists |  |

### VLib (66 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `Public` | - | carrier := r0::Public (NMT Public / NKR_TermPublic), shared with S1Lib.semanticPublic codomain | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Prefix` | - | carrier := parsed Prefix that remembers its source bytes: 129/134/142 roots are stated on bytes with parse bytes = ok pre; AspisR1PrefixAggregateParser -> AspisR1PublicPreparation via PrefixAdapter.fromOld | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Transcript` | - | carrier := SemanticTranscript<SolanaDigest> | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Challenges` | - | carrier := r1_wire::Challenges | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `OrigChallenges` | - | carrier := state_only_prefix::r0::Challenges | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `QM31` | - | carrier := canonical subtype {x : NQ // canonQ x} (needed for total qadd/qmul) | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Alpha` | - | carrier := [QM31;10] over the canonical carrier | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Claims` | - | carrier := Box<[[QM31;29];3]> | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `K29` | - | carrier := [QM31;29] | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Point` | - | carrier := SecureCirclePoint | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Record` | - | carrier := r1_wire::ValidatedRecord | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `WErr` | - | carrier := r1_wire::Error | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `VErr` | - | carrier := verifier::Error, SAME carrier as V2Lib.VErr | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `CodecErr` | - | carrier := compact::CodecError | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `View` | - | carrier := verifier::View | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Prepared` | - | carrier := verifier::Prepared | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `E29` | - | carrier := [E;29] (WideExact copy used by TX1:179/186) | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Acc` | - | carrier := verifier::Accumulator | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Geo` | - | carrier := verifier::QueryGeometry | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `Weights` | - | carrier := verifier::BatchedWeights | none | DEF | one emitted copy per carrier across all child roots; cross-copy identifications are carrier adapters |
| `qDec` | - | DecidableEq on the canonical QM31 carrier | none | DEF |  |
| `pDec` | - | DecidableEq on Point | none | DEF |  |
| `wTerminal` | - | constructor of the emitted error enum | none | DEF |  |
| `wEqualCirclePoints` | - | constructor of the emitted error enum | none | DEF |  |
| `wPublic` | - | constructor of the emitted error enum | none | DEF |  |
| `vParse` | - | constructor of the emitted error enum | none | DEF |  |
| `vSemantic` | - | constructor of the emitted error enum | none | DEF |  |
| `vAllocation` | - | constructor of the emitted error enum | none | DEF |  |
| `codecToV` | - | impl From<CodecError> for Error (candidate.rs:22): constant Parse; no ledger row (inlined); one lemma on the emitted From body | none | DEF |  |
| `debugV` | TX1:NGB001 `NIJ_ErrorJoin.source` (NIS_ErrorJoin) | NGL_ErrorModel.label (shared with V2Lib.debug) | none | ROOT, adapter new | same function as TX2:211; no TX1-side installation yet |
| `finishInputDom` | - | conjunction of the 136 child clauses that 136 cannot discharge internally (ledger NJW-caller 134/142, NKN-caller 129, NLS-bf 256 hd..asset, NLS-context) | none | ROOT, adapter new | F7: ledger clause records, not a root; several are prose and need a Lean transcription; canonicality clauses hc..hm need 129/142/150 exports or must be carried here and derived by 137 from begin |
| `publicDom` | - | NLS-bf:TX1:136:TX1:256:hd = NKR_DigestChildren.Domain (NKR_TermPublic.value pub) | NMT_ NMT_345PublicDomain.publicDomain; NMT_R2_PublicLibrary.withPublic; discharge NMT_345.validated_public_domain | ROOT, adapter exists |  |
| `semanticBytesDom` | TX1:138 `AspisR1.NGX_PrefixCarrier.fields +5` (NGX_PrefixCarrier) | NGX_PrefixCarrier.producer_domain on the byte argument | none | ROOT, adapter new |  |
| `semanticRounds` | TX1:134 `AspisR1.NJM_InvocationRoots.rounds` (NJM_InvocationRoots) | graph of the NJM rounds model at SAME (Prefix, Transcript); Cut-indexed root -> deterministic law; dom = NJW-caller 134 clauses | none | ROOT, adapter new |  |
| `claims` | TX1:129 `AspisR1.NKA_ClaimsRoot.claims` (NKA_ClaimsRoot) | graph of NKA claims reference incl. Box carrier; dom = NKN-caller 129 | none | **UNSUPPLIED/PARTIAL** | F1: root quantifies allocator/reservation; heap::uninit at r1_semantic.rs:45 returns Err(Allocation): returned law not a function of Env |
| `origChallenges` | - | struct literal (r1_semantic lines 239-246) | none | DEF |  |
| `terminalQm31` | TX1:256 `AspisR1.NLH_WrapperRoot.source` (NLH_WrapperRoot) | NLH_WrapperRoot.source law; dom = NLS-bf 256 clauses | NMT_ NMT_R2_PublicLibrary.withPublic (Public transport only) | ROOT, adapter exists |  |
| `maskValue` | TX1:076 `AspisR1.NHU_Mask.result` (NHU_Mask) | NHU_Mask.result value on canonical carriers | none | ROOT, adapter new |  |
| `validatedRecord` | TX1:141 `NFU_PrefixRecords.validated_record` (NFU_PrefixRecords) | NFU_PrefixRecords.validated_record (equation); row U8 vs Nat index adapter | none | ROOT, adapter new |  |
| `decodeK29` | TX1:147 `NGO_CallCases.claims +11` (NGO_CallCases) | NGO_CallCases / NGO_DecodeComposed value | none | ROOT, adapter new |  |
| `eta` | - | field read | none | DEF |  |
| `qadd` | TX1:024 `NEB_ArrayRefs.qm_injective` (NHV_NEB_ArrayRefs) | QM31::add Ok value on canonQ inputs, closed under canonC | none | ROOT, adapter new | F5: ledger root NEB_ArrayRefs.qm_injective is not a value law; the value law is certificate theorem NEB_QMCalls.add (+NEB_AdditiveFrames.qm_add) |
| `qmul` | TX1:029 `AspisR1.NFS_QueryLoopRoot.root` (NFS_QueryLoopRoot) | QM31::mul Ok value on canonQ inputs | none | ROOT, adapter new | F5: ledger root AspisR1.NFS_QueryLoopRoot.root is the query-loop root, not a mul law; value law is NEB_QMCalls.multiply (+NEB_FieldFrames.qm_mul) |
| `at28` | - | extra[28] | none | DEF |  |
| `state` | TX1:146 `AspisR1.NGX_StateImpl.source +1` (NGX_StateImpl) | NGX_StateImpl.source/state_effects (pure, no event) | none | ROOT, adapter new |  |
| `circle` | TX1:142 `AspisR1.NJM_InvocationRoots.circle` (NJM_InvocationRoots) | graph of NJM circle model; dom = NJW-caller 142 | none | ROOT, adapter new |  |
| `payload` | TX1:139 `AspisR1.NGX_Payload.source +1` (NGX_Payload) | NGX_Payload.source/tail_total | none | ROOT, adapter new |  |
| `c1Root` | - | *prefix.c1_root field read | none | DEF |  |
| `parsePrefix` | TX1:138 `AspisR1.NGX_PrefixCarrier.fields +5` (NGX_PrefixCarrier) | NGX_PrefixCarrier.full_result into the parsed-Prefix carrier | NMP_ parse138 full Result/type inverse at identical bytes (partial) | ROOT, adapter exists |  |
| `publicTranscript` | TX1:131 `AspisR1.NHG_Lengths.digest_domain +5` (NHG_Lengths) | NHG_Lengths/NHG_PublicCarrier/NHG_PublicTranscript with digest events from Env.sha256 | NMP_ public131 adapters, NMP_Transcription137 (partial: digest/allocation prefixes open) | ROOT, adapter exists |  |
| `begin` | TX1:150 `AspisR1.NGX_BeginDomains.cursor_step +6` (NGX_BeginDomains) | NGX_BeginDomains/NHG_BeginFrame with digest events | NMP_ begin150 adapter (partial) | ROOT, adapter exists |  |
| `filled` | TX1:064 `AspisR1.NGC_DigestBridge.forwarding +4` (NGC_DigestBridge) | heap::filled law (NGC_ReferenceValues.heap; same function as TX2:045 NIG_FilledCoverage.source) | none | **UNSUPPLIED/PARTIAL** | F1: fallible try_reserve_exact (r0/heap.rs:5-10): returned Err depends on the allocator reservation, which Env does not carry |
| `expandSemantic` | TX1:098 `NGV_AtPacket.result +11` (NGV_AtPacket) | NGV_* expansion law (src, dst) -> written dst | none | ROOT, adapter new | NMP: concrete expansion interpretation still to install |
| `expandValues` | TX1:099 `NFU_CompactLeaves.expand_result` (NFU_CompactLeaves) | NFU_CompactLeaves.expand_result | none | ROOT, adapter new |  |
| `wideView` | TX1:095 `AspisR1.NHF_ViewDecoder.result +9` (NHF_ViewDecoder) | NHF_View*/NEO_FieldView/NET_WideModel | none | ROOT, adapter new |  |
| `viewSemantic` | - | v.semantic field read | none | DEF |  |
| `parseShape` | TX1:086 `NJS_Parse.source +1` (NJS_Parse) | NJS_Parse.source (NJS_Extract = Op3I_Source copies) | none | ROOT, adapter new |  |
| `canonicalScan` | TX1:084 `NKL_ScanRoot.deployed +3` (NKL_ScanRoot) | NKL_ScanRoot.deployed/adopted/success_events | none | ROOT, adapter new |  |
| `zeroE29` | - | [E::ZERO;29] literal | none | DEF |  |
| `accNew` | TX1:174 `AspisR1.NGC_DigestBridge.forwarding +4` (NGC_DigestBridge) | Accumulator::new(S2) law (NGC cohort roots) | none | **UNSUPPLIED/PARTIAL** | F1: calls heap::filled (verifier.rs:93): Err(Allocation) reservation-dependent |
| `batchMerkle` | TX1:081 `NLN_TX1_081.root` (NLN_TX1_081) | NLN_TX1_081.root; dom = NLO-bf:TX1:094:TX1:081:64-67 (len, wire, canonical queries, rootValues) | none | ROOT, adapter new | 094 discharges dom from parseShape and from P (query range, root bindings): see F3 |
| `geometry` | TX1:181 `NFN_NFB_GeometryComposed.accepted_physical +1` (NFN_GeometryPart08) | NFN_NFB_GeometryComposed.result_state_effects | none | ROOT, adapter new |  |
| `weightsNew` | TX1:176 `NJZ_Weights.new_source` (NJZ_Weights) | NJZ_Weights.new_source (AdapterRw/VTop copy) | none | **UNSUPPLIED/PARTIAL** | F1: calls heap::filled (verifier.rs:207); ledger caller clause NKH asks for both reservation arms |
| `queryLoop` | TX1:088 `AspisR1.NFG_QueryLoopSource.complete +9` (NFG_QueryLoopSource) | NFG_QueryLoopSource.complete / NFP / NFS roots | none | ROOT, adapter new |  |
| `finish` | TX1:175 `AspisR1.NGC_DigestBridge.forwarding +4` (NGC_DigestBridge) | BatchedWeights::finish (NGC_FinishContents.contents) | none | ROOT, adapter new |  |
| `checkpoint` | TX1:186 `AspisR1.NHS_CheckpointPacket.source` (NHS_CheckpointPacket) | NHS_CheckpointPacket.source; dom := DriverEstablishedDomain (op3/op4/op7/op12 Ok, heap reservation Ok) at SAME proof | none | **UNSUPPLIED/PARTIAL** | F6: root is conditioned on predecessor results and on allocation success; the Vec abort arm named in the RSL comment is not exposed |

### PreparedNew (1 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `P (dom, law)` | TX1:179 `AspisR1.NHS_PreparedPacket.source` (NHS_PreparedPacket) | NHS_PreparedPacket.source + error/abort companions at SAME (Verified, View, g) | NMP_ fresh source call and g result (partial) | **UNSUPPLIED/PARTIAL** | F2,F3: root is Ok-arm only (premises semantic_finish, compact_check, returned = ok); 179 domain needs compact464 checked, which 087 cannot discharge |

### Env/EnvRep (5 fields)

| Field | Supplying row, root (owner module) | Representation adapter | Existing adapter | Status | Flag / note |
|---|---|---|---|---|---|
| `Env.sha256` | - | SolanaDigest via sol_sha256 (TX1:327/TX2:210 NGC_DigestBridge.forwarding) bound to the headline syscall/p1 | NNC_ NNC_RuntimeOracle, NNC_DigestTrace (partial) | TRUST |  |
| `Env.pda` | - | create_program_address reply, ruling (at) quantified slot | NND_ NND_RuntimePartial (partial) | TRUST |  |
| `Env.clock` | - | RuntimeClockSlotBinding (clock := .ok slot at TX2) | NNE_ NNE_Clock | TRUST |  |
| `EnvRep (+env1_rep, env2_rep)` | - | agreement of env with the ctx runtime oracles | NNE_ (host definitions, NNE_RecordSig) | TRUST | if the F1 fix is adopted, EnvRep also binds the reservation channel to the headline reservation binder |
| `readerHeader` | - | NLW_ReaderHeader.decode ck = some (h pr, h pub) | NNC_ NNC_ObservedLaw.accepted_header | TRUST |  |

### Transcribed helpers ((bm)(2)(c) lemmas, not fields)

| Transcription | Rows, root (owner) | Adapter state | Note |
|---|---|---|---|
| readonlyBuffer | TX1:340 `NFU_AdapterGetters.readonly` (NFU_AdapterGetters)<br>TX2:237 `NFU_AdapterGetters.readonly` (NFU_AdapterGetters) | exists in forest |  |
| readonlyAccount | TX2:236 `NHJ_ReadonlyPacket.readonly` (NIM_NHJ_ReadonlyPacket) | new |  |
| verifierCheckpoint (incl. data_len clone arm) | TX1:341 `NHJ_CheckpointPacket.substitute` (NHJ_CheckpointPacket)<br>TX2:238 `NHJ_CheckpointPacket.substitute` (NHJ_CheckpointPacket) | partial | CLOSED packet restricted to snapshot error variants (NMT, NMX: NGL_LengthCarrier.domain); Domain-True rows need the unrestricted law, i.e. the transcription itself |
| requireDistinct | TX1:339 `NHJ_DistinctPacket.three` (NHJ_DistinctPacket)<br>TX2:235 `NHJ_DistinctPacket.seven` (NHJ_DistinctPacket) | new | three (TX1) and seven (TX2) account forms |
| requireZero | TX1:342 `NFU_ZeroPort.head` (NFU_ZeroPort) | exists | frozen suffix loop vs historical index loop: NND L117 symbolic equality |
| OwnedAccount.data / data_len | TX1:335 `NHJ_DataPacket.substitute` (NHJ_DataPacket)<br>TX2:229 `NHJ_DataPacket.substitute` (NHJ_DataPacket) | partial | NMS_R2GetterLink.full gives the unrestricted getter with clone arm; NHJ_DataPacket is restricted |
| OwnedAccount.key | TX2:231 `NFU_AdapterGetters.key` (NFU_AdapterGetters) | new |  |
| snapshot | TX1:343 `NHY_SnapshotJoin.source` (NIM_NHY_SnapshotJoin)<br>TX2:239 `NHY_SnapshotJoin.source` (NIM_NHY_SnapshotJoin) | exists | NMV snapshot/window laws complete; snapAll_errs/snapAll_getters_plain in RSL_TX1_344 |
| is_active_at V1/V2 | TX2:194 `NIJ_ActiveSlots.op30_exact` (NIS_ActiveSlots)<br>TX2:196 `NIJ_ActiveSlots.op29_exact` (NIS_ActiveSlots) | new |  |
| is_paused / is_immutable V1/V2 | TX2:197 `NHY_RegistryPipeline.immutable_v1` (NHY_RegistryPipeline)<br>TX2:198 `NHY_RegistryPipeline.paused_v1` (NHY_RegistryPipeline)<br>TX2:199 `NHY_RegistryPipeline.immutable_v2` (NHY_RegistryPipeline)<br>TX2:200 `NHY_RegistryPipeline.paused_v2` (NHY_RegistryPipeline) | new |  |
| decodeMasterBox / decodeCheckpointBox | TX2:218 `AspisR1.NKY_BoxSource.master` (NKY_BoxSource)<br>TX2:216 `AspisR1.NKY_BoxSource.checkpoint` (NKY_BoxSource) | partial | native Cut/Windows/Heap roots; NMX_REMAINING: instantiate their Box/allocator representations at SAME calls |
| admitted / stage1Route | TX1:331 `NHJ_RoutePacket.associate` (NHJ_RoutePacket)<br>TX2:214 `NHJ_RoutePacket.associate` (NHJ_RoutePacket) | new | NNF_ has the route lemmas over RSL |
| decode_digest_canonical (217 body) | TX2:146 `NFY_NEQ_DecodeScalar.digest_result_state_effects` (NFY_Part005) | new |  |
| error / mapVErr | TX1:NGB001 `NIJ_ErrorJoin.source` (NIS_ErrorJoin)<br>TX2:211 `NIJ_ErrorJoin.source` (NIS_ErrorJoin) | partial | NMS_R2ErrorSource.full on TX2; CLOSED law has no format! allocation (harmless direction) |
| observer | TX1:329 `AspisR1.NJH_Observer.emitted` (NJH_Observer)<br>TX2:212 `AspisR1.NJH_Observer.emitted` (NJH_Observer) | exists | None in the release build, ruling (al) |
| r1_semantic::mark (no-op) | TX1:130 `AspisR1.NHU_Mark.effects` (NHU_Mark) | missing lemma | F8: CLOSED NHU_Mark packet is None-only; RowSpec_136/137 quantify obs; frozen body is let _=(obs,i) without detail-phases |
| verifier::mark | TX1:191 `AspisR1.NFS_QueryLoopRoot.root` (NFS_QueryLoopRoot) | exists | NEO observer root, None-only; 087/094 fix obs=None |
| transfer/withdrawal_statement_box (inside reconstruct) | TX2:227 `NFY_NEU_BoxModel.transfer` (NFY_Part056)<br>TX2:228 `NFY_NEU_BoxModel.validator` (NFY_Part056) | inside NMS_R2PoolSites.reconstruct |  |

## 5. Instantiation order and scope estimate

The dependency order is in the `order` list of LIB0_MAP.json, and LIB0_BRIEF.md gives the module list. It runs in two lanes after a common base.
- **Base:** LIB_Carriers, then LIB_Env, LIB_Deployed, LIB_ErrorDebug, LIB_Root0 and LIB_Transcribed.
- **TX2 lane,** following the TX2 principal (217, 234 → 233 → 242 → 241):
  - LIB_PoolCarriers;
  - LIB_PoolRegistry (needed by 234);
  - LIB_PoolAccounts (233);
  - LIB_PoolDecoders and LIB_PoolEffects (242/241);
  - LIB_PoolLib, LIB_Tx2Auth and LIB_V2Lib.
- **TX1 lane,** following the TX1 principal (136 → 137 → 087 → 094 → 328 → 345):
  - LIB_VCarriers;
  - LIB_VField, LIB_VRecords and LIB_VParse;
  - LIB_VSemantic (136/137);
  - LIB_VPrepare and LIB_Prepared (087);
  - LIB_VTx1A, LIB_VTx1B and LIB_VLib (094);
  - LIB_S1 (345).
- **Then:** LIB_Instances.

**Scope estimate.**
- 26 modules.
- About 140 focused single-file Lean scopes, range 110-200. That is 2-4 each for definitional and bundle modules, and 6-10 each for the VLib child modules, which carry most of the copy bridges.
- Plus one focused combined import and one own-root raw axiom audit at the end.
- 0 Kani and 0 extraction. The F4 association relies on the existing extraction item and adds no extraction.
- F1 and F2 need lead rulings first. Until then, LIB_Prepared and the five F1 fields stay parameters, and the other 98 fields can be completed.
