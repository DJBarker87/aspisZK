# TCK top-of-stack integration check

Target not yet established. This report is an integration audit. It closes no row, removes no premise and adds no trust. Base: `research` at d7168a6b898 (RSL_ at 62a00100f9d, NMT_ support merged after it). Every source was read with `git show research:<path>`; the frozen code was read at 4bb3b3f51e16.

## 0. Verdict

The headline will not compose once all 18 rows close as they are currently briefed. Three things block it.

1. **Root0 is circular at the top (G1).** NMF_GameRoot obtains Root0 from facts that hold only because the headline's binder `extraction` holds at the TX2 occurrence. The rows give `extraction` for the actual code only when Root0 already holds. Section 2 traces the exact Lean steps. The repair is a Root0-free native lemma chain that can be proved from existing CLOSED roots. It needs no new trust. No job owns it.
2. **`extraction` cannot be literally discharged.** The binder is a universally quantified equation. The rows give refinement only on their own domains, and for TX2 that domain includes Root0. The top therefore has to instantiate `native1`/`native2` with the AdapterRw models, which makes `extraction.stage1/.stage2` hold by `rfl`. All native content then moves to `accepted1`, `accepted2`, `game.recorded` and the entry identity. Several adapters are needed for that move: A1/A2 (RSL Ref to AdapterRw/DrvC slots), A3/A4 (stage wrappers to `S2W_D189Wrappers.first/second`) and A5 (the entry dispatch to `CPP_Invocation.native`). No job owns any of them.
3. **The phantom ledger edges would fail the gate (section 5).** That failure would block TX2:233 and TX2:240, and through the composed-row semantics it would also block 242, 241, 221, 213 and TX1:333/330.

None of these is a counterexample to soundness, and none needs a new trust row.

## 1. The headline: its exact statement and binders

`AspisR1.RPx_Deployed.deployed` (evidence/root-transport-20261110/NMF_HEADLINE_SOURCE.txt; the kernel statement is unchanged from evidence/replay-deployed2-20261027/RPx_Deployed.lean). Its binder block, verbatim:

```
theorem deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (missing : Uninstalled CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)
    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
```

The conclusion has eleven conjuncts. They include the P6 boundary, the driver and SDK equalities, `FJv_DResult.Outcome …` (the native-accepted outcome with the charged `BinRawByteCollisionTargets.event … (Q0+Q1+2965) …` alternative), and the claims and numeric bounds `failureModel runtime ≤ (Q0+Q1+1)/2^100` for Q0+Q1 ≤ maxQueries. They also include the copy facts (`saved.val.length = 1768`, …), Rc2_Events, the CPH Protection/Trace/Recorder facts and S6N_Installation.

The binders that speak about the deployed execution are the ones ruling (ao)(3) names:
- `extraction` (with its fields `stage1`, `stage2` and `digestSource`);
- `admission1/2`, together with the identity of `e1/e2`, `data1/data2` and `slot` with what the runtime hands the ELF;
- `accepted1/2`;
- `game` together with `RuntimePersistence`;
- `queries`, which is L154 and a statement parameter.

The relevant definitions are quoted below.

- `S2W_ExtractionBoundary.First := Program → Accounts → Slice U8 → Result (core.result.Result (alloc.vec.Vec U8) Cuts.PE)` and `Second := Program → Accounts → Slice U8 → Slot → Result (core.result.Result Unit Cuts.PE)`. These are the owned functions stage1_owned (TX1:345) and stage2_owned (TX2:241).
- `S2W_DigestExtraction.AeneasExtraction ops native1 native2 hashv` has three fields:
  - `stage1 : ∀ program accounts data, native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data`;
  - `stage2 : ∀ program accounts data slot, native2 … = AdapterRw.r1_pool_adapter.owned.stage2_owned ops …`;
  - `digestSource : ∀ self parts, ops.op43 self parts = digest hashv self parts`.
- `S2W_D189Wrappers.first native copy allocator e program data state` does four things in order: it reserves `admittedSizes e 3 firstSizes`, calls `native program e.first data`, copies the result into account 2 through `copy` (where `.panic` becomes `.fail`), and then cleans up. `second` reserves `admittedSizes e 7 secondSizes`, calls `native program (e.second secondSizes) data slot` and cleans up; it has no writes. These are hand models of TX1:344 and TX2:240.
- `CPH_Game.DeployedPairExecution` has fields (a) `consecutive`, (b) `checkpoint`, (c) `parent` and (d) `recorded`. Field (d) is `CPG_RuntimeTrace.Executes n1 n2 copy allocator id … (p.actions t) …` together with the same statement for `u`. Its `Step.invoke` uses `CPP_Invocation.native n1 n2 copy allocator id store input`. That function dispatches on `Hiq_ReleaseRoute.route data`, which is `stage1` ⇔ `data = [3,10] ∨ [3,11]`, or `asq8` ⇔ `data.take 4 = "ASQ8"`. It also checks the count (3 or 7) and then calls the D189 wrappers. Only the store and the event of the result enter `Step`; the Err code does not.

## 2. Question 1: Root0

### 2.1 Where Root0 enters

- `NLP_InputDomain.Root0 ck proof := (ck.val.drop 112).take 32 = (encodeState ((SemanticRecordCodec.decodeState (OraclePortCompactDraft.slice (bytesOf proof.val) 16 32)).getD (fun _=>0))).val` (evidence/tx2-common-20261110/NLP_InputDomain.lean).
- `NMN_064.Domain` has the fields `proofExtent`, `checkpointExtent`, `publicBound` and `root0 : NLP_InputDomain.Root0 a.checkpoint a.proof`. `NMN_064.root (domain : Domain s.args) : RowSpec H s`.
- `NLT_CompleteRoot.root … (proofLength) (publicLength) (root0 : NLP_InputDomain.Root0 ck proof)`. In its proof, `root0` is consumed ONLY by `NLT_C04NativeInstalled.installed`, `NLT_ReplyInstalled.installed`, `NLT_Chronology.installed` and `NLT_C04StopChronology/StopParent.installed` (the batch-Merkle C04 installation). The result and event equations come from `NLT_NativeSource.source … proofLength …`. The resume law `NLT_AllocationInstalled.resume` and `NLT_NativeFacts.resume_scope` do not use Root0.
- The RSL carriers are as follows. RowSpec_241's (D2) is `V.Root0 ck (slice pr AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES)` when `pr.length = 58295`. RowSpec_240's (D2') is the same statement on `payload a6 s` and `payload a0 s` for 7 accounts at lengths 1768/58295. RowSpec_221's (P2) and RowSpec_213's (E1), given by `TX2_213.Domain V S1 a s := (admitted → ¬stage1Route → TX2_240.Domain V a s) ∧ (admitted → stage1Route → S1.dom a s)`, carry (D2') to the entry state. The frozen source checks digests but never compares root bytes (NLP_FINDINGS.md: verifier.rs:393–431, candidate.rs:294–303).

### 2.2 What NMF proves

`NMF_GameRoot.root0_or_existing_collision` takes the headline's binder block unchanged (NMF_BINDER_IDENTITY.json) and concludes:

```
∃ f s, SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s ∧
  NLP_InputDomain.Root0 saved.deref f.proof ∧ bytesOf s.checkpoint.val=bytesOf saved.val ∧
  ((NLP_InputDomain.Root0 s.checkpoint s.proof ∧ (57607 → ≤1880 → NLT_CompleteRoot.RowSpec …)) ∨
   BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P) F3X_Projection.project select)))
```

It speaks of the same occurrence: `s` comes from the cuts of `e2.second secondSizes`, so `SourceCuts.checkpoint2Index` is accounts2[6] and `secondRange` is accounts2[0][688..finish]. These are the carriers of (E1), up to representation. The collision event is the headline's existing charged event. As a Lean statement, therefore, NMF adds no hypothesis.

### 2.3 Why NMF does not discharge (E1) for the actual program

NMF reaches its Root0 branch through three model-run facts, and all three come from `extraction.stage2` at the TX2 occurrence:
- `original` is the headline's `FJv_DResult.Outcome`. `FJv_DNativeAccepted.accepted` builds it from `FJv_DFinalSource.source … extraction …`.
- The cut `s` exists only through `S2W_NativeConsolidation.cuts_of_acceptance`, which performs `rw [extraction.stage2] at accepted2`. Its field `second : ops.op11 (…Digest32 ops) s.pub s.proof s.checkpoint () none = ok (.Ok ())` is the model's TX2:064 call (op11 in the cohort dictionary).
- `readerHeader := NMF_ReachedHeader.returned … oracle s.pub s.proof s.checkpoint tx2 calls` takes `calls : Cons_Native.Calls base finish reserved query geo D hash pub proof ck t`, which is the cohort reader `Tx2N_Install.reader_success`.

In the final composition the rows are supposed to supply exactly these model facts for the actual code: 241, 240, 221 and 213 over the NMN_064 root for op11. They supply them only under (D2)/(E1)/Dom064.root0. Using NMF to discharge (E1) is therefore circular.

The ∀ form of `extraction.stage2` cannot simply be retained for the actual native2 either. Where Root0 fails, the native resume reads root0 from checkpoint[112..144], while the cohort fixes committedRoot0 from proof[16..48] (NLP_FAILING_STEP.md, NLP_ResumeRoots.returned and NLP_RootDomain.mismatch). If the header digests also coincide on such inputs, the two can diverge. No reached counterexample was constructed. The ∀ equation is unsupported on those inputs and is not expected to hold.

### 2.4 What is missing (exact) and whether it is provable

The missing items are not trust items and not binder mismatches. They are four lemmas, plus a case split.

- **G1a (Root0-free weak root of TX2:064).** For all inputs satisfying the three extents (no Root0), every native outcome of 064/065 satisfies a weak law: the result and events equal `NJJ_Common.run f.resume f.pending …` with the CLOSED resume law at the native records. If 064 returns Ok, the resume comparison passed, which gives `NLW_ReaderHeader.decode (bytesOf ck) = some (H (bytesOf proof), H (bytesOf pub))`. This is provable from existing CLOSED or candidate pieces: `NLT_NativeSource.source`, `NLT_AllocationInstalled.resume`, `NLT_NativeFacts.resume_scope`, `NMN_064.parser` and `NMN_OracleFold`, with `CheckpointBytes4Comparison.successful_calls` and `NLW_ReaderHeader.calls` used on the native resume. The weak law must drop the C04 items. Lean only, no Kani.
- **G1b (parametric parent roots).** RowSpec_241/240/221/213 take `V : V2Lib` as a parameter. If NMS_, NMV_ and NMW_ prove their roots for every `V` whose `tx2auth` the actual 064 call refines on `Dom064 V`, the weak instance below is free. `TCK_WeakRoot0.weaken V w := { V with Root0 := fun _ _ => True, tx2auth := w }`. TCK_WeakRoot0 proves that under it 240's and 213's domains are unconditional and 241's domain is (D1) only (`domain240_weaken`, `domain213_weaken`, `entry_weak_unconditional`). If they prove the roots only for the canonical `V`, G1b is a restatement per row.
- **G1c (NMF′).** NMF re-proved from native facts. Take `s`'s account reads and range from the weak 241/242 roots (242's domain is `True`), replace `second` and `calls` by G1a, and keep TX1's writer header (the TX1 rows carry no Root0) and `persistent` from RuntimePersistence and `game`. The conclusion is unchanged: Root0 or the existing charged event. `P2P_NativeSelection.on_cuts` must be checked to see whether it uses the `second` field of SourceCuts. If it does, a SourceCuts variant without that field is needed.
- **R0-rep.** A representation lemma: `bytesOf s.checkpoint = payload a6 s_entry`, `bytesOf s.proof = slice (payload a0 s_entry) 688 58295`, and `V2Lib.Root0 := fun ck pr => NLP_InputDomain.Root0 ⟨ck⟩ ⟨pr⟩` on byte carriers (RSL_CHECK item 1). It goes through the snapshot law (TX2:239), since no write precedes the snapshot.
- **Case split.** The row conclusion is used only in the Root0 branch. In the event branch the top relies on the existing charged event. This is sound because the event (`P2P_Charge.binding_or_collision` on the recorded joint program) does not depend on TX2's native behaviour once the matched digests come from G1a.

Everything needed comes from existing CLOSED roots, the NMN_ candidate and the approved RuntimePersistence row. No trust is proposed.

## 3. Question 2: the other own-input clauses that reach the top

| Clause | Origin | Discharged by | Owner | Top-level residue |
|---|---|---|---|---|
| proof 57607 (Dom064, NLT factory, `NLG-upstream:*:TX2:124:native-input` at 064/241/240/221/213) | 064/065/resume | Inside TX2:241: `scan_proof_buffer` sets `proof_length = verifier::PROOF_BYTES` (enters as `L.scanProof`, CLOSED), then Ref_241 checks `proofData.length != proofEnd` | NMS_ | none. Ledger must record `discharged_by` = 241 root at the 213/221/240 NLG-upstream ids |
| checkpoint 1768 | 064 | 233 `verifierCheckpoint v` (v = accounts[6], `data_len = CHECKPOINT_BYTES`) plus (D1) | NMS_ (via NMX_ 233 law) | none |
| public ≤ 1880 | 064, resume | Ref_241 check `publicBytes.length != STATEMENT_BYTES` | NMS_ | none |
| (D1) snapshot consistency | 241 | 240 snapshot (CLOSED TX2:239, transcribed) | NMV_ | none |
| Root0 (D2/D2'/P2/E1) | 064 | not in the program; G1 + NMF′ at the selected occurrence | **none** | G1 |
| TX1:136 `finishInputDom` (NJW 134/142, NKN 129 own clauses; NLS-bf:256 hc/hp/hz/hl/hchi/ht/hm) | 136's children | 137, from `Prefix::parse` (138), `public_transcript` and `begin`; the canonical challenges come from the draw laws | NMP_ (137), NMO_ (136 internal part) | none if derivable; otherwise an (aq)(3) child lemma in 137's children |
| `publicDom` = `NKR_DigestChildren.Domain (NKR_TermPublic.value pub)` ∧ `asset_id < 2147483647` | NLS-bf:TX1:136:TX1:256:hd/asset | propagates 137→087→094→328→345. At 345 it comes from the decode (canonical digests) and the validate step. The frozen `validate_common` checks `digest_is_canonical` on anchor_root and nullifier, and `asset_id.0 >= P → Err` | NMT_ (345) | small child lemma if the CLOSED TX1:332/276 laws do not export recipient/change/frontier/nextRoot/nextFrontier canonicality |
| `semanticBytesDom` | 138 | 087, from the `expand_semantic` law | NMP_ | none |
| 087 R1/R2/R3, 094 T1/T2, 094 public 1880 | 087/094 | 094 parse (086/084); observer() = None (TX1:329, CLOSED under (as)(3)); the 345 statement snapshot (1880) | NMT_ | none |
| 094 `NLO-bf:TX1:094:TX1:081:64–67` (len/wire/canonical/rootValues, CALLER_OWNED_OPEN) | batch_merkle | TX1:179 Prepared::new law | NMT_ | an (aq)(3) child lemma if 179 does not export the root bindings |
| NMT_'s proposed 094 clauses `i.digest = NLV_Deployed.digest missing indexError reservation`, `∀ parts, i.digest.digest () parts = i.hashv parts` (NMT_CALLER_CLAUSES.json) | 094 | not in the program: they mention headline configuration, which (bf)(3) forbids as an own-input clause | NMT_ to restate as a SAME-argument clause (328 passes SolanaDigest, ruling (al)) | interpretation moves to A0 at the top |

Two clauses have no owner: Root0 (G1) and the configuration-digest interpretation (A0, inside G0).

## 4. Question 3: the instantiation chain

Recommended form of the top (G0). Instantiate `native1 := AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c)` and `native2 := AdapterRw.r1_pool_adapter.owned.stage2_owned (sdk c)`. Then `extraction.stage1/.stage2` hold by `rfl`, and `digestSource` follows from the configuration's op43 and the choice of `hashv` (A0). Each physical-association binder is then supplied from the actual pair by the row roots plus the adapters below. In the event branch of G1c the top concludes the charged event directly. Ruling (ao)(3)(a)'s P6/D188 option-A transport stays as reclassified trust for each native cut, as it is now.

| Headline binder | Row roots that supply it | Missing adapter | Recommended owner |
|---|---|---|---|
| `native1`, `extraction.stage1` | 345 ← 328 ← 094 ← 087 ← 137 ← 136 | **A1**: Ref_345/Ref_328 ≡ `AdapterRw.stage1_owned/first_decoded (sdk c)` under the RSL↔Aeneas carrier map, and Ref_094 (with its CLOSED cohort children) ≡ `(sdk c).op10` at the call (ruling (s) slot instance). Includes fresh-emission ≡ AdapterRwModel emission per definition, which overlaps the planned (bk) re-extraction campaign | new job (model bridge); unowned |
| `native2`, `extraction.stage2` | 241 ← 242 ← 233 ← {234, 217}; 064 (candidate) | **A2**: Ref_241/242/233/234 ≡ AdapterRw `stage2_owned/validate_asq8/authenticate_asq8_accounts/authenticate_invariant_release_registry (sdk c)`; `V2Lib.tx2auth` (NMN_064 law, End/chronology → Result) ≡ `(sdk c).op11` at the call; decoder slots of `missing` (op23, op25–34, op48/49; decode_lane = 217) instantiated by the native decoders under ruling (s)(i)(ii) | same job as A1; unowned |
| `extraction.digestSource`, `hashv`, `syscall` | none (configuration) | **A0**: `(sdk c).op43 = hashv` by choosing `hashv`/`missing.op43`; RuntimeSyscall for that `hashv`; NMT_'s digest clauses | G0 |
| `accepted1` | 344 (+ the 345 chain) | **A3**: the Ok arm of RowSpec_344 implies `S2W_D189Wrappers.first native1 copy allocator e1 verifier data1 state1 = ok (.Ok (saved,post1,final1))`. Needs: RSL `SdkState` ↔ `e1.heap` (from RuntimeEntrypointAdmission); the three snapshots (58295/1880/1768) ↔ `admittedSizes e1 3 firstSizes` and `e1.first`; the write event ↔ `copy`/TrustedStd and `release (exclusiveGuard …)`; `state1/final1` from the actual Allocator item (RSL leaves allocator internals out of the obligations) | new job (physical adapter); unowned (NMV_ brief: roots only) |
| `accepted2` | 240 (+ the 241 chain) | **A4**: the same for `second`, plus Clock reply ↔ `slot` (RuntimeClockSlotBinding) and post2 = `e2.heap`. Needs Root0 at the occurrence (G1) | physical-adapter job; unowned |
| `game.recorded` (d), `game.consecutive` (a) | 330/213 ← 333/221 ← 344/240 | **A5**: for every verifier invocation in `p.actions t` and `p.actions u`, the actual effect has the store and event of `CPP_Invocation.native`. Dispatch facts: `admitted` + process + stage1's `accounts.len() != 3` / stage2's `!= 7`, magic, coincide with `Hiq_ReleaseRoute.route` and the count tests (frozen r1_pool_adapter_owned.rs:447–466), and the Err codes are irrelevant to `Step`. **G2**: a Root0-free write frame for every non-selected ASQ8 invocation, from the weak 240/241 instance (TCK `domain240_weaken`). The Pool side of (d) stays with Stream C (NIB-P1..P4) | physical-adapter job + G1b; unowned |
| `admission1/2`, identity of e1/e2/data/slot | entry rows 330/213 | entry-state representation (part of A3–A5); the admission rows remain trust | physical-adapter job |
| Root0 at TX2 (E1) | NMN_064 (candidate) + 241…213 | **G1a/G1b/G1c + R0-rep** (section 2.4) | G1a: TX2 verifier owner (NMN_ successor, Lean only); G1b: brief amendment to NMS_/NMV_/NMW_; G1c: G0 job |
| `RuntimePersistence` | none | none (approved row, consumed by NMF/NMF′ unchanged) | — |
| `sdk`, `std`, `allocator`, `p1`, `syscall` | none | the RSL SDK model ≡ NLF_RefCell/SdkModel/ParentModel (RSL_CHECK item 1), inside A3–A5 | physical-adapter job |
| `queries` | none | none (L154 parameter) | — |
| `L`, `missing`, `indexError`, `reservation`, `D`, `a`, `words`, `prior`, `root`, `length`, `Q0`, `Q1`, `H`, `sha256` | none | `missing` must be exhibited per ruling (s) (inside A2) | — |

NMW_HEADLINE.md is confirmed. The dispatcher folds discharge no binder by themselves. They feed A5, and through 344/240 they feed A3/A4.

## 5. Question 4: phantom ledger edges

Ledger24 (NLX_LEDGER.json.xz) shows the following:
- TX2:233 has `caller_domain_obligations`:
  - `call-domain:programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts->crates/aspis-core/src/field.rs::M31::to_le_bytes` (TX2:016; required_named_hypotheses `NCS_R050.PacketDomain`, `.PhysicalInterpretation`);
  - `…->crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes` (TX2:039; `NCS_R073.*`).
  Both have `status: OPEN` and `discharged_by: null`.
- TX2:240 has `call-domain:…::stage2->crates/aspis-core/src/r0/domain.rs::FibreIndex::get` (TX2:043; `NDT::local::NDH::04.*`), also `OPEN` with `discharged_by: null`.

Each requires "Prove this actual use establishes the selected callee PacketDomain…". There is no actual use. Frozen r1_pool_adapter_owned.rs:293 is `&checkpoint.checkpoint_sequence.to_le_bytes()` on a `u64` field (pair_forest_accounts.rs:154), which is core `u64::to_le_bytes`. Line 479 is `Clock::get()` (solana_program `Sysvar::get`, imported at r1_pool_adapter.rs:45). The check that a parent discharges every caller clause of every child would therefore fail at 233 and 240. Under the composed-row semantics (ruling (as)), that failure would keep 242, 241, 221, 213, TX1:333 and TX1:330 OPEN: TX1:333's canonical callees include `stage2`.

Proposed reclassification, wording per (az)(1), for the next ledger:

> TX2:233 → TX2:016 (M31::to_le_bytes) and TX2:233 → TX2:039 (WideExact::to_le_bytes): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. The frozen body (r1_pool_adapter_owned.rs:293, 4bb3b3f51e16) calls core `u64::to_le_bytes` on `checkpoint.checkpoint_sequence : u64` as a PDA seed. It never calls a field or wide-exact `to_le_bytes`. The edge is a name-collision artifact. Under the never-remove rule it is kept visible in the inventory with this evidence. The u64 conversion is a safe std operation under ruling (au). It executes inside the parent cut, transcribed as `RSL.u64le`, and is not a child row.
>
> TX2:240 → TX2:043 (FibreIndex::get): RECLASSIFIED_SPURIOUS_BY_NAME, edge retained. Line 479 is `Clock::get()` (the solana_program Clock sysvar), not `FibreIndex::get`. The actual call is the Clock syscall slot (`Event.clock`/`Env.clock` in RSL_TX2_240), bound by the existing runtime row RuntimeClockSlotBinding. No trust change.

Related reporting correction (addition only). RuntimeClockSlotBinding names its consumer as `r1_pool_adapter.rs:910 (Clock::get()?.slot)`. That is the non-owned validate copy. The deployed TX2 route is `owned::stage2` (r1_pool_adapter.rs:945–962 `mod owned; use owned::{stage1, stage2}`), and its consumer is r1_pool_adapter_owned.rs:479. The row text should add that consumer. The row's statement does not change.

The NLG-upstream resume-extents clause at 213/221/240 is real, not phantom. It is discharged at 241 (section 3), and the ledger must record that with `discharged_by`.

## 6. Unowned gaps (recommended owner, size)

| Gap | What | Owner | Size |
|---|---|---|---|
| G1a | Root0-free weak root of 064/065 (result/events/resume law; Ok ⇒ header matched) | TX2 verifier successor of NMN_ (Lean only) | small–medium, about 10 Lean scopes, 0 Kani |
| G1b | 241/240/221/213 roots proved parametric in `V2Lib` | brief amendment to NMS_, NMV_, NMW_ now | nil if done now; one restatement per row later |
| G1c + R0-rep | NMF′ from native facts; byte representation of Root0 at the entry | top-assembly job | medium, about 15–25 Lean scopes (NMF used 18) |
| G2 | Root0-free no-write frame for non-selected ASQ8 invocations | NMV_ (from the weak instance) | small |
| A1/A2 | RSL Ref ≡ AdapterRw/DrvC model; op10/op11/`missing` slot instances; fresh vs AdapterRwModel emission | new model-bridge job (or the Opus agent) | medium–large, about 40–60 Lean scopes |
| A3/A4/A5 | stage wrappers → D189 `first/second`; entry dispatch → `CPP_Invocation.native`; SdkState/allocator representation | new physical-adapter job, after the NMV_/NMW_ packets | medium, about 30 Lean scopes |
| A0 + G0 | top assembly theorem (native := model; event branch) and digest/hashv instance | top-assembly job | small–medium once the above exist; one 16 GiB aggregation scope |
| L1 | ledger reclassifications (section 5), `discharged_by` for the NLG-upstream ids, Clock consumer line | next ledger job after NMQ_ | small |

## 7. Would the headline compose once all 18 rows close?

No, not as currently briefed. Even with every row CLOSED, `extraction` has no supportable instance for the actual native2, and (E1) has no non-circular discharge. With G1, A0–A5, G2 and G0 delivered the composition has a sound shape: the Root0 branch goes through the rows and the event branch through the existing charge. All of these come from existing CLOSED roots, the approved RuntimePersistence row and the existing trust rows. Target not yet established.

## 8. Validation actually run

- RSL_ rebuilt locally from 62a00100f9d sources, in the worktree's ignored `.lake/`: 20 modules (RSL_Audit not rebuilt), final exit 0 for each, at most 729 MB RSS per file, 0 swaps. Toolchain leanprover/lean4:v4.31.0 (commit 68218e87). One earlier attempt on RSL_TX1_344 exited 1 because I compiled it before RSL_TX2_221, which it imports. That was a build-order error on my side, with no source change; the module compiled once the order was corrected.
- `TCK_WeakRoot0.lean` compiled with `lake env lean ../top-check-20261107/TCK_WeakRoot0.lean` from evidence/rowspec-lead-20261107: exit 0, wall 0.22 s, peak RSS 402,030,592 B, 0 swaps, core Lean plus RSL only. Its `#print axioms` output is in TCK_WEAKROOT0_OUTPUT.txt: `propext` and/or `Quot.sound` only.
- No host, Kani, extraction or combined-import run. Every statement about non-RSL Lean objects comes from reading source, not from compiling it.
