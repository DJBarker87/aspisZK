# ARV root comparison — proposal, not adoption

Target not yet established. No `ARV_Root.deployed` theorem is asserted.
`ARV_Root.Proposed` is only a type-checked proposed formula. Actual before/after
Rc10 declarations remain identical; the ledger earns zero removals.

The table below gives the COMPLETE declarations side by side. Shared namespace
openings are those in lean/Rc10_Top.lean and lean/ARV_Root.lean; no binder,
conclusion, failure event, or numerical constant is elided. The right side is
unproved and is not an unchanged-quantifier deletion.

| Before: Rc10_Top.deployed | Proposed after: ARV_Root.Proposed |
|---|---|
| `theorem deployed {W A CoreError Tx : Type}` | `def Proposed : Prop := ∀ {W A CoreError Tx : Type}` |
| `    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)` | `    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)` |
| `    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))` | `    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))` |
| `    (std : TrustedStd copy) (allocator : Allocator A)` | `    (std : TrustedStd copy) (allocator : Allocator A)` |
| `    (e1 e2 : Entry) (w1 w2 : W)` | `    (e1 e2 : Entry) (w1 w2 : W)` |
| `    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)` | `    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)` |
| `    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)` | `    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)` |
| `    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)` | `    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)` |
| `    (reservation : NP6_StdModel.Reservation)` | `    (reservation : NP6_StdModel.Reservation)` |
| `    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)` | `    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)` |
| `    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)` | `    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)` |
| `    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)` | `    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)` |
| `    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)` | `    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)` |
| `    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)` | `    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)` |
| `    (data1 data2 : Slice U8)` | `    (data1 data2 : Slice U8)` |
| `    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)` | `    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)` |
| `    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))` | `    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))` |
| `    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =` | `    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =` |
| `      ok (.Ok (saved,post1,final1)))` | `      ok (.Ok (saved,post1,final1)))` |
| `    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =` | `    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =` |
| `      ok (.Ok (post2,final2)))` | `      ok (.Ok (post2,final2)))` |
| `    (root : Array U8 32#usize) (length : U32)` | `    (root : Array U8 32#usize) (length : U32)` |
| `` | `` |
| `    (prior : Program Bytes State Unit)` | `    (prior : Program Bytes State Unit)` |
| `    (words : CanonicalCutEnrichedTranscript.Words)` | `    (words : CanonicalCutEnrichedTranscript.Words)` |
| `    (p : CPG_Projection.Observations Tx A) (t u : Tx)` | `    (p : CPG_Projection.Observations Tx A) (t u : Tx)` |
| `    (actions : List (CPP_BankState.Action A))` | `    (actions : List (CPP_BankState.Action A))` |
| `    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)` | `    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)` |
| `    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw` | `    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw` |
| `      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)` | `      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)` |
| `      (CPG_Projection.tentative p)` | `      (CPG_Projection.tentative p)` |
| `      (CPG_Projection.success p) (CPG_Projection.loaded p))` | `      (CPG_Projection.success p) (CPG_Projection.loaded p))` |
| `    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)` | `    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)` |
| `    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)` | `    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)` |
| `    (runtime : F3T_Runtime.Runtime)` | `    (a : SCE_Experiment.Adversary A)` |
| `    (finishOwners : FIp_GlobalOwners.Owners` | `    (finishOwners : FIp_GlobalOwners.Owners` |
| `      (FIp_Install.configuration indexError c reservation)` | `      (FIp_Install.configuration indexError c reservation)` |
| `      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)` | `      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)` |
| `    (binding : F3T_Runtime.StoredCarrierBinding` | `    ,` |
| `      (FIp_Install.configuration indexError c reservation) D` | `    let runtime := ART_Runtime.runtime (FIp_Install.configuration indexError c reservation)` |
| `      (F3T_Installed.source (FIp_Install.configuration indexError c reservation) hashv) P runtime)` | `      hashv copy allocator CPH_Program.verifier a;` |
| `    :` | `    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=` |
| `    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=` | `      fun _ => P2P_NativeSelection.pair` |
| `      fun _ => P2P_NativeSelection.pair` | `        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))` |
| `        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))` | `        CPH_Program.verifier e1 e2 data2 slot;` |
| `        CPH_Program.verifier e1 e2 data2 slot;` | `    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H` |
| `    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H` | `      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧` |
| `      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧` | `    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧` |
| `    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧` | `    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =` |
| `    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =` | `      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase` |
| `      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase` | `        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry` |
| `        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry` | `        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧` |
| `        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧` | `    (FIs_Result.Outcome L e1 e2 w1 w2` |
| `    (FIs_Result.Outcome L e1 e2 w1 w2` | `      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase` |
| `      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase` | `      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query` |
| `      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query` | `      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase` |
| `      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase` | `      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)` |
| `      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)` | `      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H` |
| `      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H` | `      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior` |
| `      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior` | `      (p.physicalEvents t) hashv` |
| `      (p.physicalEvents t) hashv` | `      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)` |
| `      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)` | `        (eval H (Hiq_RecordedJoint.program` |
| `        (eval H (Hiq_RecordedJoint.program` | `          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv P)` |
| `          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv P)` | `          F3X_Projection.project select)))) ∧` |
| `          F3X_Projection.project select)))) ∧` | `    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧` |
| `    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧` | `      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧` |
| `      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧` | `      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧` |
| `      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧` | `      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧` |
| `      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧` | `      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →` |
| `      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →` | `        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧` |
| `        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧` | `      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧` |
| `      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧` | `        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧` |
| `        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧` | `    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧` |
| `    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧` | `      saved.val.length = 1768 ∧` |
| `      saved.val.length = 1768 ∧` | `      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧` |
| `      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧` | `      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧` |
| `      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧` | `      post1.counter = e1.heap.counter ∧` |
| `      post1.counter = e1.heap.counter ∧` | `      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧` |
| `      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧` | `    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧` |
| `    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧` | `    CPH_Protection.Facts p t saved CPH_Program.verifier ∧` |
| `    CPH_Protection.Facts p t saved CPH_Program.verifier ∧` | `    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧` |
| `    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧` | `    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator` |
| `    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator` | `      CPH_Program.verifier H p t u saved ∧` |
| `      CPH_Program.verifier H p t u saved ∧` | `    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))` |
| `    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))` | `` |

## Exact quantifier and image audit

The independent `(runtime : F3T_Runtime.Runtime)` universal quantifier is replaced
by `(a : SCE_Experiment.Adversary A)` and the definition
`runtime := ART_Runtime.runtime cfg hashv copy allocator CPH_Program.verifier a`.
Every other binder, including independent P, its original first-only query bound,
and finishOwners, is textually unchanged. The binding binder is absent in the
proposal. P is NOT silently identified with submission a. No carrier, auxiliary
source-recorder event, failure functional or constant is changed by this proposal.

Instantiating Runtime at a **proved actual deployed image** would specialise the
system, without restricting the adversary, if every allowed deployed adversary,
outcome law and full cost had a representative. The current `ART_Runtime.runtime`
is a failure-aware partial-source observer, with exact evaluation theorem
`ART_Runtime.eval_runtime`. It is NOT yet proved to be that actual deployed image
for all accepted worlds. `ARV_OneTuple.obstruction` disproves the blanket support
claim required by that identification, even with one supported original tuple.
It therefore cannot honestly be described as a proved deployed specialisation.

The exact D188/extraction/P6C predecessors are
`S2W_DigestExtraction.AeneasExtraction` (stage1, stage2, digestSource),
`GExq_InstalledWrapper.first_source`, `GExq_InstalledWrapper.second_source`,
`P6C_Issued.installed`, `P6C_Whole.same_cuts`, and the query-only replacement
`ARU_Whole.same_cuts`. They establish installed source erasure and issued-query
SDK correspondence on their actual cuts. None quantifies over arbitrary bank
histories and proves `ART_Runtime.runtime` is the whole deployed probability law.
`ARU_OriginalFactory.original` and `ARU_OriginalLaw.exact` preserve a supplied native
bank tuple on its own queried-address cylinder. Their SupportedEntry input cannot
be obtained from arbitrary partial-experiment acceptance by applying the factory
to that same acceptance. This is the exact failed expected route.

The proposal introduces no new **syntactic hypothesis**, but it is unproved.
Repairing its application would require proving actual bank/admission support
through a generative game/refinement, associating P with the chosen a's submission,
and deriving full adaptive/rejected-prefix cost from the game's work budget.
Adding those as caller hypotheses would be new premises, not discharges. Replacing
P and queries by submission a and ART_AdversaryWork.Bound would additionally change
quantifiers/work coverage; it is NOT the requested sole Runtime specialisation.
`ARQ_ChoiceCoverage.unbounded_choice` proves why the unchanged first-only query
binder does not supply the latter bound.

The exploratory `ARV_Filter.runtime` is explicitly noncomputable. Its Eligible
test drops unsupported accepted observations and retains their entire query log;
it is neither shipped source nor an adopted runtime image. It is not used to
prove this root proposal. Any later adoption needs an execution/law equivalence
proof, not a rename of the filtered probability law as deployed.

Actual result: no ARV_Root.deployed and no ART_Top.deployed are claimed.
L159/L185 and L181 remain in Rc10. The lead may use this packet to choose a
proper bank-generated root and cost interface; no contract adoption is inferred.

## Supported native cost counterexample (checked040)

`ARV_NativeCostGap.obstruction` strengthens the first-only coverage diagnosis.
Given a supported native tuple for a, retained extraction, and the SAME original
`∀ H, (eval H (submission a)).1.length ≤ Q`, it constructs b with:

- exactly the same submission program and original first-only bound;
- a supported native bank/game/admission/persistence tuple and accepted partial
  account at the original native world;
- full reached adversary work strictly greater than Q, hence failure of the
  `ART_AdversaryWork.Bound ... b Q` consumed by the account mass theorem.

The construction inserts Q+1 ignored-response queries before the second choice.
Inputs, native successes and the original physical game are unchanged; every
inserted query remains charged. This class IS allowed by the approved adaptive
game. It is not an attack or a counterexample to the numerical security bound;
it is a checked failure of deriving the needed full-work interface from the
unchanged first-only query binder. No stronger bound may be silently assumed.
