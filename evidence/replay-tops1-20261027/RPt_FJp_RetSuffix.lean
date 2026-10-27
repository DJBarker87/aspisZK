import RPz7_FIs_P2P_Deployed
import RPz7_FIs_P2P_Extract
import RPz7_FIs_P2P_FinalResult
import RPz7_FIs_P2P_FinalTop
import RPz7_FIs_P2P_R5Close
import RPz7_FIs_P2P_R6Result
import RPz7_FIs_P2P_Release
import RPz7_FIs_P2P_SafResult
import RPz7_FIs_P2P_SafTop
import RPz7_FIs_P2P_Source
import RPt_FJp_RetPrefix

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_SafResult
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem strengthen {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit)
    (old : FJp_Ret_R3Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,initial,selected,publicFacts,parser,
    acceptance,nonvacuity,caller⟩ := old
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,initial,selected,publicFacts,parser,
    acceptance,nonvacuity,?_⟩
  have ⟨_,_,_,_,_,_,_,_,_,success,_⟩ := calls.1
  apply SAF_C_SAF_LiteralCaller.strengthen (old := caller) (success := success)

#print axioms strengthen
end AspisR1.FJp_Ret_SafResult
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_SafTop
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem deployed {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (Rc3_Install.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (Rc3_Install.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (Rc3_Install.configuration c reservation).stageBase) (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry)) (Rc3_Install.configuration c reservation).finish) (Uni_Install.current (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry) (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (words : CanonicalCutEnrichedTranscript.Words) :
    DrvC_Implementation.driver (Rc3_Install.configuration c reservation) =
      DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (Rc3_Install.configuration c reservation) =
      SdkD_PairBatches.dictionary (Rc3_Install.configuration c reservation).adapter
        (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).stageBase
        (Rc3_Install.configuration c reservation).finish (Rc3_Install.configuration c reservation).reserved
        (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry
        (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std ∧
    (let r := Rc3_Install.configuration c reservation
    let source := GExp_Experiment.program
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
      (DrvC_Installation.stage r) r.reserved r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r) (DrvC_Installation.digest r) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100)) ∧
    (FJp_Ret_SafResult.Outcome L e1 e2 w1 w2 (Rc3_Install.configuration c reservation).adapter (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry (Rc3_Install.configuration c reservation).stageBase (Rc3_Install.configuration c reservation).finish c.boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc3_Install.configuration c reservation)) prior) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc3_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (Rc3_Install.configuration c reservation) native1 native2 copy allocator program := by
  obtain ⟨driverEq,sdkEq,headline,original,copyFacts,events,protection⟩ := FJp_Ret_R3Top.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c reservation native1 native2
    primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project words
  refine ⟨driverEq,sdkEq,headline,?_,copyFacts,events,protection⟩
  apply FJp_Ret_SafResult.strengthen (old := original)

#print axioms deployed
end AspisR1.FJp_Ret_SafTop
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_FinalResult
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem strengthen {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit)
    (old : FJp_Ret_SafResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,initial,selected,publicFacts,parser,
    acceptance,nonvacuity,caller⟩ := old
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,initial,selected,publicFacts,parser,
    acceptance,nonvacuity,?_⟩
  apply SAF_C_SAF_PreparedCaller.strengthen (base := AuS1_Install.base stageBase)
    (reader := calls.1.1) (old := caller)

#print axioms strengthen
end AspisR1.FJp_Ret_FinalResult
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_FinalTop
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem deployed {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (Rc3_Install.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (Rc3_Install.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (Rc3_Install.configuration c reservation).stageBase) (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry)) (Rc3_Install.configuration c reservation).finish) (Uni_Install.current (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry) (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (words : CanonicalCutEnrichedTranscript.Words) :
    DrvC_Implementation.driver (Rc3_Install.configuration c reservation) =
      DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (Rc3_Install.configuration c reservation) =
      SdkD_PairBatches.dictionary (Rc3_Install.configuration c reservation).adapter
        (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).stageBase
        (Rc3_Install.configuration c reservation).finish (Rc3_Install.configuration c reservation).reserved
        (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry
        (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std ∧
    (let r := Rc3_Install.configuration c reservation
    let source := GExp_Experiment.program
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
      (DrvC_Installation.stage r) r.reserved r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r) (DrvC_Installation.digest r) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100)) ∧
    (FJp_Ret_FinalResult.Outcome L e1 e2 w1 w2 (Rc3_Install.configuration c reservation).adapter (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry (Rc3_Install.configuration c reservation).stageBase (Rc3_Install.configuration c reservation).finish c.boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc3_Install.configuration c reservation)) prior) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc3_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (Rc3_Install.configuration c reservation) native1 native2 copy allocator program := by
  obtain ⟨driverEq,sdkEq,headline,original,copyFacts,events,protection⟩ := FJp_Ret_SafTop.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c reservation native1 native2
    primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project words
  refine ⟨driverEq,sdkEq,headline,?_,copyFacts,events,protection⟩
  apply FJp_Ret_FinalResult.strengthen (old := original)

#print axioms deployed
end AspisR1.FJp_Ret_FinalTop
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_Deployed
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem deployed {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (Rc3_Install.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (Rc3_Install.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (Rc3_Install.configuration c reservation).stageBase) (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry)) (Rc3_Install.configuration c reservation).finish) (Uni_Install.current (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry) (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (words : CanonicalCutEnrichedTranscript.Words) :
    DrvC_Implementation.driver (Rc3_Install.configuration c reservation) =
      DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (Rc3_Install.configuration c reservation) =
      SdkD_PairBatches.dictionary (Rc3_Install.configuration c reservation).adapter
        (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).stageBase
        (Rc3_Install.configuration c reservation).finish (Rc3_Install.configuration c reservation).reserved
        (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry
        (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std ∧
    (let r := Rc3_Install.configuration c reservation
    let source := GExp_Experiment.program
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
      (DrvC_Installation.stage r) r.reserved r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r) (DrvC_Installation.digest r) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100)) ∧
    (FJp_Ret_FinalResult.Outcome L e1 e2 w1 w2 (Rc3_Install.configuration c reservation).adapter (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry (Rc3_Install.configuration c reservation).stageBase (Rc3_Install.configuration c reservation).finish c.boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc3_Install.configuration c reservation)) prior) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc3_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (Rc3_Install.configuration c reservation) native1 native2 copy allocator program := by
  exact FJp_Ret_FinalTop.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c reservation native1 native2
    primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project words

#print axioms deployed
end AspisR1.FJp_Ret_Deployed
end

section
set_option autoImplicit false
open Lean Meta Elab Tactic

/-- Proof refactoring only: inline the two checked root theorem bodies, select
source conjuncts, and require every unprovided legacy argument to disappear.
The resulting ordinary Lean term is kernel checked. No fact is admitted. -/
elab "fjp_retain_extract_source" : tactic => do
  let root ← mkConstWithFreshMVarLevels ``AspisR1.FJp_Ret_Deployed.deployed
  let info ← getConstInfo ``AspisR1.FJp_Ret_Deployed.deployed
  let some rootBody := info.value? true | throwError "Root has no checked body"
  let names := [``AspisR1.FJp_Ret_FinalTop.deployed,
    ``AspisR1.FJp_Ret_SafTop.deployed, ``AspisR1.FJp_Ret_R3Top.deployed,
    ``AspisR1.FJp_Ret_LiteralTop.deployed]
  let mut body := rootBody
  for nm in names do
    let ci ← getConstInfo nm
    let some value := ci.value? true | throwError "Missing checked predecessor"
    body := body.replace fun e =>
      if e.isConstOf nm then some (value.instantiateLevelParams ci.levelParams e.constLevels!)
      else none
  let mut proof := body.instantiateLevelParams info.levelParams root.constLevels!
  let mut ty ← inferType root
  let lctx ← getLCtx
  while ty.isForall do
    let .forallE n d b _ := ty | unreachable!
    let localArg := lctx.foldl (init := none) fun found decl =>
      if decl.userName == n then some decl.toExpr else found
    let arg ← match localArg with
      | some e => pure e
      | none => mkFreshExprMVar d
    proof := mkApp proof arg
    ty := b.instantiate1 arg
  let mut parts : Array Expr := #[]
  for i in [:6] do
    let p ← withTransparency .reducible (whnf proof)
    unless p.getAppFn.isConstOf ``And.intro do
      throwError "Expected root conjunction at {i}: {p}"
    let args := p.getAppArgs
    parts := parts.push args[2]!
    proof := args[3]!
  parts := parts.push proof
  -- Rc2: driver, dictionary, obsolete headline, source, copy, events, protection.
  let kept := #[parts[0]!,parts[1]!,parts[3]!,parts[4]!,parts[5]!]
  let mut out := kept[4]!
  for i in [0:4] do
    out ← mkAppM ``And.intro #[kept[3-i]!,out]
  out ← instantiateMVars out
  if out.hasMVar then
    for mv in ← getMVars out do
      logInfo m!"Remaining: {(← mv.getType)}"
    throwError "A legacy argument remains in the source proof"
  let goal ← getMainGoal
  goal.assign out
  replaceMainGoal []

end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_Source
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem source {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (Rc3_Install.configuration c reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (Rc3_Install.configuration c reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (Rc3_Install.configuration c reservation).stageBase) (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry)) (Rc3_Install.configuration c reservation).finish) (Uni_Install.current (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry) (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
 :
    DrvC_Implementation.driver (Rc3_Install.configuration c reservation) =
      DrvC_SourceEntry.source (Rc3_Install.configuration c reservation) hashv ∧
    DrvC_Installation.sdk (Rc3_Install.configuration c reservation) =
      SdkD_PairBatches.dictionary (Rc3_Install.configuration c reservation).adapter
        (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).stageBase
        (Rc3_Install.configuration c reservation).finish (Rc3_Install.configuration c reservation).reserved
        (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry
        (Rc3_Install.configuration c reservation).boundaries (Rc3_Install.configuration c reservation).std ∧
    (FJp_Ret_FinalResult.Outcome L e1 e2 w1 w2 (Rc3_Install.configuration c reservation).adapter (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry (Rc3_Install.configuration c reservation).stageBase (Rc3_Install.configuration c reservation).finish c.boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc3_Install.configuration c reservation)) prior) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc3_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved := by
  fjp_retain_extract_source

#print axioms source
end AspisR1.FJp_Ret_Source
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_R5Close
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem from_saf {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (input : DrvC_Installation.Configuration F CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (Rc5_Install.configuration indexError input reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator program)
    (system : S2W_ExtractionBoundary.Program) (programNotSystem : program ≠ system)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (original :
    FJp_Ret_FinalResult.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError input reservation).adapter (Rc5_Install.configuration indexError input reservation).currentBase
      (Rc5_Install.configuration indexError input reservation).reserved (Rc5_Install.configuration indexError input reservation).query
      (Rc5_Install.configuration indexError input reservation).geometry (Rc5_Install.configuration indexError input reservation).stageBase
      (Rc5_Install.configuration indexError input reservation).finish input.boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError input reservation)) prior) :
    FJp_Ret_R5Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError input reservation).adapter (Rc5_Install.configuration indexError input reservation).currentBase
      (Rc5_Install.configuration indexError input reservation).reserved (Rc5_Install.configuration indexError input reservation).query
      (Rc5_Install.configuration indexError input reservation).geometry (Rc5_Install.configuration indexError input reservation).stageBase
      (Rc5_Install.configuration indexError input reservation).finish input.boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError input reservation)) prior
      (p.physicalEvents t) := by
  let c := Rc5_Install.seed indexError input
  have keyLaw := Rc5_Install.key indexError input reservation
  have oldGame := CPH_Game.recordedInstance game
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,initial,selected,publicFacts,sourceFacts,
    acceptance,nonvacuity,caller⟩ := original
  have cuts := base.1
  let version := CPG_History.on_cuts (game := oldGame)
    (c := Rc5_Install.configuration indexError input reservation) (keyLaw := keyLaw) (extraction := extraction)
    (std := std) (notSystem := programNotSystem) (accepted1 := accepted1) (accepted2 := accepted2)
    (RuntimePersistence := RuntimePersistence) (f := f) (s := s) (cuts := cuts)
  have writerKey : version.key = (e1.handles 2).1 := by
    change ((p.layout t).handles 2).1 = _
    rw [game.consecutive.2.1]
    rfl
  have readerKey : version.key = (e2.handles 6).1 := by
    change ((p.layout t).handles 2).1 = _
    rw [game.consecutive.2.2]
    exact game.checkpoint.1
  have events : version.events = p.physicalEvents t := by
    change (CPP_BankHistory.run native1 native2 copy allocator program
      (CPR_SourceBank.afterCopy (CPG_Projection.cached (p.bank t)) ((p.layout t).handles 2).1 saved) actions).2 = _
    exact congrArg Prod.snd (CPG_RuntimeTrace.result game.recorded.1.2.2)
  have owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (Rc5_Install.configuration indexError input reservation).currentBase)
        (Rc5_Install.configuration indexError input reservation).reserved
        (Rc5_Install.configuration indexError input reservation).query
        (Rc5_Install.configuration indexError input reservation).geometry
        (F3M_CircleSource.install input.boundaries) (NP6_StdModel.calls reservation)) :=
    SAP_PrepareOwner.installed _ input.boundaries (NP6_StdModel.calls reservation)
  have ports := SAQ_Decoder.primitives input.query
  have oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest
      (SdkD_PairBatches.current (Rc5_Install.configuration indexError input reservation).adapter
        (Rc5_Install.configuration indexError input reservation).currentBase
        (Rc5_Install.configuration indexError input reservation).stageBase
        (Rc5_Install.configuration indexError input reservation).finish
        (Rc5_Install.configuration indexError input reservation).reserved
        (Rc5_Install.configuration indexError input reservation).query
        (Rc5_Install.configuration indexError input reservation).geometry
        (F3M_CircleSource.install input.boundaries) (NP6_StdModel.calls reservation)))) () H := by
    intro parts digest returned
    change (DrvC_Installation.sdk (Rc5_Install.configuration indexError input reservation)).op43 () parts=ok digest at returned
    rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
    exact (syscall.returningValue parts digest returned).trans (p1.realization _)
  have encoding := Rc4_Encoding.derive _ _ _ _ _ () _ _ _ _ _ run owner ports H oracle
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,encoding,base,initial,selected,TxS_RawPublic.of_typed f.pub f.proof publicFacts,sourceFacts,
    version,writerKey,readerKey,events,S2X.checkpoint_persistence _ _ version,?_,?_,?_⟩
  · obtain ⟨i,pub,proof,tag,size,fit,yes⟩ := acceptance
    exact ⟨i,pub,proof,tag,size,fit,fun p2prime => yes version p2prime⟩
  · exact nonvacuity version
  · exact Rc5_Caller.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ input.boundaries
      (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H
      f s outer pre middle fs ss run prior tx2 indexError input.query input.geometry rfl rfl version caller

#print axioms from_saf
end AspisR1.FJp_Ret_R5Close
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_R6Result
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem strengthen {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit) (events : List S2X.AccountEvent)

    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError)) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (source : FJp_Ret_R5Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events) : Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,caller⟩ := source
  have safe := P6C_OnCuts.same_cuts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved f s base.1
  have whole := P6C_FullBoundary.same_cuts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) native1 native2 hashv extraction sha256 H p1 syscall
    e1.first (e2.second secondSizes) saved f s base.1
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
      (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact base.1
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps
      reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  have ⟨cuts,writer,reader,multi,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  let words := CanonicalCutEnrichedTranscript.wordsFromMaps (fun _=>none) (fun _=>none) (fun _=>none)
  have packet := PFin_Packet.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps
    (F3M_CircleSource.install B) (NP6_StdModel.calls reservation) e1.first (e2.second secondSizes) saved f s
    pairCuts selected run header1.2.2.1 H native1 native2 hashv pairExtraction sha256 p1 syscall words scanned.2.2
  have joined := Rc6_Caller.from_cut L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B
    (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
    pairCuts selected header1.2.2.1 scanned.2.2 native1 native2 hashv pairExtraction sha256 p1 syscall caller
  exact ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,packet,safe,whole,joined⟩

#print axioms strengthen
end AspisR1.FJp_Ret_R6Result
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_Release
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open FS FS2
theorem remove {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit) (events : List S2X.AccountEvent)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    {X : Type} (account : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H account).1 ≤ Q+1921)
    (source : FJp_Ret_R6Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv) :
    let installed := sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)
    let select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair installed program e1 e2 data2 slot
    FJp_Ret_Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program account project select))) := by
  dsimp only
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,acceptance,nonvacuity,packet,safe,whole,caller⟩ := source
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,?_⟩
  have association := P2P_NativeSelection.on_cuts _ program e1 e2 data2 slot saved f s base.1 origin
  have alternative := P2P_Charge.binding_or_collision account project
    (fun _ => P2P_NativeSelection.pair (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) program e1 e2 data2 slot) Q budget H
  rcases alternative with bad | good
  · exact Or.inl bad
  · right
    rw [association] at good
    have p2prime : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub := ⟨good⟩
    obtain ⟨i,pub,proof,tag,size,fit,yes⟩ := acceptance
    exact ⟨⟨i,pub,proof,tag,size,fit,yes p2prime⟩,nonvacuity p2prime,caller p2prime⟩

#print axioms remove
end AspisR1.FJp_Ret_Release
end
