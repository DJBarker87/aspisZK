# ARX proposed root comparison

`ARX_Root.deployed` is proved, not adopted. The actual adopted root remains
`Rc10_Top.deployed` until lead/owner review. This packet changes no shipped bytes.

## Binder and law changes

All binders except those listed here are retained verbatim, including SDK/std,
allocator, extraction, native/hash boundary, fixed native pair and admissions,
bank game, RuntimePersistence and global finish owners.

| Rc10 | ARX |
|---|---|
| independent `P : ByteProver` | arbitrary `a : SCE_Experiment.Adversary A`; `P := ARW_Induced.program native1 copy allocator verifier a` |
| `queries : ∀ H, (eval H P).1.length ≤ Q0+Q1` | `queries : ∀ H, (ARW_Induced.issued native1 copy allocator verifier a H).length ≤ Q0+Q1` |
| independent `runtime : F3T_Runtime.Runtime` | `runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a` |
| `binding : F3T_Runtime.StoredCarrierBinding ... P runtime` | removed; no replacement hypothesis |

The only changes are the `(runtime,binding,P)` to `(a, admitted runtime at a,
induced P, Q = a's issued-query budget)` replacement. Q0+Q1 is a uniform upper
budget, not an assertion that every path makes exactly Q calls. Both adaptive
phases, duplicate reads and reached rejected prefixes remain issued work.

From `let select` through the final conclusion, the source declarations are
byte-identical (checked offline). Every numerical constant and the extractor
failure event is retained. The numerical proof can upper-bound the model using
the first-only `submission a` because its issued cost is at most the full cost;
the account charge retains the actual adaptive second choice and all prefixes.

The runtime's admitted cylinder predicate existentially supplies the *own*
bank tuple, both admissions, game and persistence in `ARU_Support.At`. They are
semantic membership data inside the defined observer, not universal hypotheses
or claims that Rc10's independent fixed tuple belongs to every adversary.
`ARX_Domain.range` and `ARX_Coverage.coverage` make this exact. The observer
records the complete original query log in every world. It returns None outside
admission, and exactly the original RunView on admitted worlds. Its mean is
zero-extended with original weights, with NO conditioning or normalization.
The scan-failure term is still added once, conservatively.

The accepted unsupported poison class is outside the approved game and outside
this observer's range (`excludes_poison`). Rejected-source paths keep identical
issued logs and zero mass (`ARX_RejectedPrefixes`). No literal all-world ART
runtime law or equality of its global mean with the admitted mean is claimed.

## Conservativity qualification

`ARX_Conservativity.conservativity` is unconditional on the old pure-second-choice
class, with identical P and budgets, at the admitted runtime. The old
`ARW_OldRoot.conservativity` has a premise `ARW_Root.Requested` for the *unfiltered*
ART runtime. Literal instantiation of that theorem does not type-compose with
the authorised runtime change. We supply the admitted counterpart, rather than
silently equating the two means. The old class itself contains the poison
adversaries, so it does not imply all-world admission. This is an explicit limit
of deliverable (5)'s literal wording, not a counterexample to the numeric bound.

## Complete before: Rc10_Top.deployed

```lean
theorem deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)
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
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (P : F3T_ByteCarrier.ByteProver) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : F3T_Runtime.Runtime)
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)
    (binding : F3T_Runtime.StoredCarrierBinding
      (FIp_Install.configuration indexError c reservation) D
      (F3T_Installed.source (FIp_Install.configuration indexError c reservation) hashv) P runtime)
    :
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase
        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry
        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧
    (FIs_Result.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
```

## Complete after: ARX_Root.deployed

```lean
theorem deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)
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
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)
    :
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase (FIp_Install.configuration indexError c reservation).stageBase
        (FIp_Install.configuration indexError c reservation).finish (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query (FIp_Install.configuration indexError c reservation).geometry
        (FIp_Install.configuration indexError c reservation).boundaries (FIp_Install.configuration indexError c reservation).std ∧
    (FIs_Result.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError c reservation).adapter (FIp_Install.configuration indexError c reservation).currentBase
      (FIp_Install.configuration indexError c reservation).reserved (FIp_Install.configuration indexError c reservation).query
      (FIp_Install.configuration indexError c reservation).geometry (FIp_Install.configuration indexError c reservation).stageBase
      (FIp_Install.configuration indexError c reservation).finish (FIp_Install.boundaries c.boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError c reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError c reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError c reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError c reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
```

## Atomic recount

The recount re-enumerates Rc10's atomic leaves/families and keeps
`L185 = L159` as an alias. `ARX_LEDGER_DELTA.json` records every row.

| Scope | Rc10 before | Proposed ARX after |
|---|---|---|
| Actual antecedent | 83T / 12P / 13G / 0C | 83T / 11P / 13G / 0C |
| Distinct deployment-inclusive | 89T / 16P / 13G / 0C | 89T / 14P / 13G / 0C |

Proposed removals: **L159 (alias L185)** and **L181**, two distinct P rows;
added 0, reclassified 0. L159's whole-run binding is replaced by proved admitted
carrier and failure domination rather than being repackaged as a hypothesis.
L181's experiment/native-prefix association is supplied on the exact admitted
range, preserving all issued prefixes and zero rejected mass. This credit is
for the authorised admitted model: it does not establish source-to-ELF
correspondence, all-world unfiltered ART support, or a coherent release replay.
The actual adopted Rc10 statement remains unchanged: actual adoption delta 0.

## Conditional non-vacuity and precise fixture waits

`ARX_Nonvacuity.conditional` transports the SAME JFx proof/public bytes on the
supplied own native tuple/cylinder into an accepted admitted RunView. It does
not fabricate the missing joint full accepted native pair at FIp's installation.
The exact existing partial predecessors to compose are:

- `JFm_ChallengeFixture.inhabited`, `JFm_Begin.source`, `JFm_RealTrace.source`,
  `JFm_Rounds.source`;
- `JFn_TX2.partial_on_saved`, `JFn_Nonvacuity.inhabited`;
- `JFr_ArithmeticFixture.inhabited`, `JFr_TX2_Partial.on_saved`,
  `JFr_TX2_CircleAfterDots.source`;
- `JFs_PublicFixture.inhabited`, `JFs_PublicDecode.source`,
  `JFs_PublicValidation.source`, `JFs_ExactSerialization.source`,
  `JFs_ExactInitialization.source`;
- `JFu_Installation.extraction`, `JFu_Installation.oracle`,
  `JFu_AfterstateValidator.source`;
- `JFv_RuntimeWitness.compatible`, `JFv_SampledFixture.inhabited`,
  `JFv_ClaimsFixture.inhabited`, `JFv_SemanticCall.success`,
  `JFv_SemanticChain.success`;
- `JFw_RealExpansion.inhabited`, `JFw_TypedPrefix.inhabited`,
  `JFw_Y1.inhabited`.

These are partial predecessor theorems, not a completed real-byte pair theorem.
In particular JFu's extraction has its own seeded installation, and JFv's
compatible runtime tuple does not supply the whole installed native pair.
The remaining task is their same-input/same-installation joint composition,
including complete TX2 query/batch/finish success. No nonexistent completed
pair theorem is cited. Conditional non-vacuity is retained as the lead requested.

## Representation implementation detail for review

The admitted runtime is represented as an ordinary causal ROM program with
an outcome-support decision on its complete recorded cylinder. Its arguments
are the installed native/library/configuration/adversary parameters. The bank
tuple, admissions, game and persistence are the *per-execution membership
witness*, existential inside `permitted`; `on_admitted`/`coverage` take that own
tuple as their argument. This realizes the admitted-world range within the
existing `F3T_Runtime.Runtime` type without adding an oracle-aware program
constructor, an arbitrary measure, a trusted support factory, or a fixed tuple
promise for every a. It is a noncomputable semantic observer, not a new shipped
bank admission algorithm. Review the exact definition in the kernel receipts.

`ARX_LawConstants.unchanged` separately checks Q+34 / Q+1161 / Q+2322 /
Q+2965 on the induced model and admitted account. `ARX_OldClassPoison.differs`
checks that a pure-choice adversary can have an accepted ART RunView excluded
from the admitted range. Thus even pure-choice conservativity does not erase
the declared change of global runtime functional. This fact does not show a
deployed attack or refute the unfiltered numeric inequality.
