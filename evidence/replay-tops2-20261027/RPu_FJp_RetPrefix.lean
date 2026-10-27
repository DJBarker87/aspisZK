import RPz7_FIs_P2P_ActualPair
import RPz7_FIs_P2P_ClosedPair
import RPz7_FIs_P2P_DirectPair
import RPz7_FIs_P2P_LiteralPair
import RPz7_FIs_P2P_LiteralTop
import RPz7_FIs_P2P_PairSelected
import RPz7_FIs_P2P_R3Top
import RPu_FJp_RetDefinitions

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_PairSelected
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps B claimsStd))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) B claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    :
    FJp_Ret_ResultSelected.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  unfold FJp_Ret_ResultSelected.Outcome
  obtain ⟨f,s,outer,pre,middle,fs,ss,cuts,origin,selected,writer,reader,multiproof,scanY,checkY,
    scan,oldTx1,batches,tx2,first,expanded,owned,layout,unchanged,before1,before2,claims,caller⟩ :=
    P2P_NativePair.accepted_pair_unified L sdk copy std allocator e1 e2 w1 w2
      admission1 admission2 adapterOps ops reserved queryOps geoOps (AuS1_Install.base stageBase) finishOps
      B claimsStd native1 native2 prepareOwner primitiveOwner hashv extraction
      sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 p root length
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
      e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd)
      native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  obtain ⟨run,rootView,rootRange,rootCopy⟩ := SdkD_PairBatches.first_run adapterOps ops stageBase finishOps
    reserved queryOps geoOps B claimsStd e1.first (e2.second secondSizes) saved f s pairCuts
  have rootBinding : FJp_RootBinding.Holds f.proof run.root := ⟨rootView,rootRange,rootCopy⟩
  have control := Tx1Q_Control.fields _ _ _ _ _ _ _ _ _ _ _ run
  have proofLength : f.proof.val.length = 57607 := by
    simpa only [bytesOf,List.length_map] using cuts.proofLength
  have publicLength := (WAdm_Public.reached _ _ B claimsStd e1 _ saved f s cuts).2
  have domain := WAdm_Domain.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner proofLength publicLength
  obtain ⟨fields,size,canonical⟩ := WAdm_Inventory.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner
  have nativeContent := WAdm_NativeInstall.on_run _ _ _ _ _ _ _ _ _ _ _ run prepareOwner primitiveOwner
  have sourceContent : WAdm_SourceWriter.writer
      (Tx1Q_Install.digest (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd))
      (Tx1Q_Carriers.prepared run.p)
      (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub () = ok saved := by
    rw [WAdm_SourceWriter.writer_eq _ _ _ _ _ _ fields size canonical control.2.2.1]
    exact run.writer_call
  obtain ⟨tx2run,enriched,aux⟩ := FIs_Cons_Second.accepted adapterOps ops stageBase finishOps reserved queryOps geoOps
    B claimsStd e1.first (e2.second secondSizes) saved f s cuts
  have calls := enriched.1
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2run,origin,enriched,?_,selected,?_⟩
  · unfold Cons_Base.Outcome
    refine ⟨cuts,writer,reader,multiproof,scanY,checkY,scan,?_,batches,?_,first,expanded,owned,layout,
      unchanged,before1,before2,claims⟩
    · exact ⟨control.1,control.2.1,control.2.2.1,control.2.2.2.1,control.2.2.2.2,
      run.writer_call,domain,WAdm_Carrier.wide _ _ _ _ domain,sourceContent,nativeContent⟩
    · exact ⟨tx2.1,tx2.2.1,tx2.2.2.1⟩
  · refine ⟨T2R_PublicDecode.facts f.pub f.proof f.statement cuts.decode,?_⟩
    unfold SAF_C_T2R_CallerSource.Outcome
    dsimp only
    intro runtime p2prime entry
    obtain ⟨parsed,facts,sites,oldOutcome⟩ := caller runtime p2prime entry
    obtain ⟨version,key,ledger,events,sameCheckpoint,sameProof,samePub,savedLength⟩ :=
      RowOrder_History.on_d189_cuts copy std allocator e1 e2 _ native1 native2 hashv extraction
        program data1 state1 final1 saved post1 accepted1 f s cuts CPhy_Header.decode H writer reader runtime p2prime
    obtain ⟨tr,authParsed,parseReached⟩ := entry.parsed
    have parser := (OraclePortStoredParserC4.parsed _ _ _ parseReached).1
    obtain ⟨frame,frameRead,target,auth⟩ := AuS1_OnRun.same_pair prior adapterOps ops stageBase finishOps
      reserved queryOps geoOps B claimsStd native1 native2 hashv pairExtraction sha256 H p1 syscall
      e1.first (e2.second secondSizes) saved f s pairCuts sameCheckpoint sameProof authParsed parser
      run rootView rootRange rootCopy
    refine ⟨parsed,facts,sites,?_⟩
    unfold SAF_C_T2R_ContSource.Outcome
    intro queryLeaves geoLeaves domain multiply one inverse
    have old := oldOutcome queryLeaves geoLeaves domain multiply one inverse
    refine ⟨authParsed,frame,parser,frameRead,target,?_,?_⟩
    · intro ports q tr data rho prepare read geo domain multiply one inverse
      rcases auth data rho q prepare with collision | indexed
      · exact Or.inl collision
      · exact Or.inr (Tx1Q_Model.ten _ _ _ _ _ _ _ _ _ _ _ run
          ports
          authParsed q tr data rho prepare read (OraclePortCompactDraft.parse_header _ _ parser).2 proofLength
          (OraclePortAllSelectedRecoveryC6.recovered _ frame authParsed 2) indexed
          geo domain multiply one inverse)
    · have proofLength2 : s.proof.val.length = 57607 := by
        have lengths := congrArg List.length sameProof
        simpa only [bytesOf,List.length_map,proofLength] using lengths
      apply SAF_C_T2R_Finish.strengthen (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps _ ()
        s.checkpoint s.proof s.pub saved tx2run.p2 tx2run.saved2 _ tx2run.v2 H
        (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed _ calls.1
      exact SAF_C_Cons_FinishProof.strengthen (AuS1_Install.base stageBase) finishOps reserved queryOps queryLeaves
        geoOps geoLeaves domain multiply one inverse _ () s.pub s.proof s.checkpoint saved H
        (bytesOf f.proof.val) (bytesOf f.pub.val) run.p authParsed _ frame
        ((OraclePortCompactDraft.parse_header _ _ parser).2.trans sameProof.symm)
        sameCheckpoint proofLength2 tx2run calls aux auth

#print axioms accepted
end AspisR1.FJp_Ret_PairSelected
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_ActualPair
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (words : CanonicalCutEnrichedTranscript.Words) :
    FJp_Ret_ActualResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  have prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) :=
    SAP_PrepareOwner.installed
      (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved queryOps geoOps) B claimsStd
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
    FJp_Ret_PairSelected.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps (F3M_CircleSource.install B)
      claimsStd native1 native2 prepareOwner primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length
  have ⟨cuts,writer,reader,multiproof,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps
      reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,?_⟩
  intro history p2prime entry
  obtain ⟨parsed,facts,sites,continuation⟩ := caller history p2prime entry
  refine ⟨parsed,facts,sites,?_⟩
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,ten,finish⟩ :=
    continuation queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨version,key,ledger,events,sameCheckpoint,sameProof,samePub,savedLength⟩ :=
    RowOrder_History.on_d189_cuts copy std allocator e1 e2 _ native1 native2 hashv extraction
      program data1 state1 final1 saved post1 accepted1 f s cuts CPhy_Header.decode H writer reader history p2prime
  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩
  exact SAF_C_SAP_SourceConsumer.from_cut adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
    e1.first (e2.second secondSizes) saved f s pairCuts selected run header1.2.2.1 H
    native1 native2 hashv pairExtraction sha256 p1 syscall words scanned.2.2 _ authParsed parser
    sameProof.symm tx2 ten finish

#print axioms accepted
end AspisR1.FJp_Ret_ActualPair
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_ClosedPair
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (words : CanonicalCutEnrichedTranscript.Words) :
    FJp_Ret_ClosedResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
    FJp_Ret_ActualPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps B
      claimsStd native1 native2 primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length words
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,?_⟩
  intro history p2prime entry
  obtain ⟨parsed,facts,sites,continuation⟩ := caller history p2prime entry
  refine ⟨parsed,facts,sites,?_⟩
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,source⟩ :=
    continuation queryLeaves geoLeaves domain multiply one inverse
  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩
  exact SAF_C_SAP_CloseConsumer.close adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
    saved f s run H _ authParsed tx2 native1 native2 hashv pairExtraction sha256 p1 syscall source

#print axioms accepted
end AspisR1.FJp_Ret_ClosedPair
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_DirectPair
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (words : CanonicalCutEnrichedTranscript.Words) :
    FJp_Ret_DirectResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
    FJp_Ret_ClosedPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps B
      claimsStd native1 native2 primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length words
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,?_⟩
  intro history p2prime entry
  obtain ⟨parsed,facts,sites,continuation⟩ := caller history p2prime entry
  refine ⟨parsed,facts,sites,?_⟩
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,source⟩ :=
    continuation queryLeaves geoLeaves domain multiply one inverse
  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩
  exact SAF_C_SAP_DirectConsumer.direct adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
    saved f s run H _ authParsed tx2 source

#print axioms accepted
end AspisR1.FJp_Ret_DirectPair
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_LiteralPair
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (words : CanonicalCutEnrichedTranscript.Words) :
    FJp_Ret_LiteralResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
    FJp_Ret_DirectPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps B
      claimsStd native1 native2 primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length words
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,?_⟩
  intro history p2prime entry
  obtain ⟨parsed,facts,sites,continuation⟩ := caller history p2prime entry
  refine ⟨parsed,facts,sites,?_⟩
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,source⟩ :=
    continuation queryLeaves geoLeaves domain multiply one inverse
  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩
  exact SAF_C_SAP_LiteralConsumer.literal adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd
    saved f s run H _ authParsed tx2 source

#print axioms accepted
end AspisR1.FJp_Ret_LiteralPair
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_LiteralTop
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
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (SAP_Install.configuration c).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (SAP_Install.configuration c).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (SAP_Install.configuration c).stageBase) (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query (SAP_Install.configuration c).geometry)) (SAP_Install.configuration c).finish) (Uni_Install.current (SAP_Install.configuration c).currentBase (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query (SAP_Install.configuration c).geometry) (SAP_Install.configuration c).boundaries (SAP_Install.configuration c).std) native1 native2 hashv)
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
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (SAP_Install.configuration c) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (SAP_Install.configuration c) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (words : CanonicalCutEnrichedTranscript.Words) :
    DrvC_Implementation.driver (SAP_Install.configuration c) =
      DrvC_SourceEntry.source (SAP_Install.configuration c) hashv ∧
    DrvC_Installation.sdk (SAP_Install.configuration c) =
      SdkD_PairBatches.dictionary (SAP_Install.configuration c).adapter
        (SAP_Install.configuration c).currentBase (SAP_Install.configuration c).stageBase
        (SAP_Install.configuration c).finish (SAP_Install.configuration c).reserved
        (SAP_Install.configuration c).query (SAP_Install.configuration c).geometry
        (SAP_Install.configuration c).boundaries (SAP_Install.configuration c).std ∧
    (let r := SAP_Install.configuration c
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
    (FJp_Ret_LiteralFull.Outcome L e1 e2 w1 w2 (SAP_Install.configuration c).adapter (SAP_Install.configuration c).currentBase (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query (SAP_Install.configuration c).geometry (SAP_Install.configuration c).stageBase (SAP_Install.configuration c).finish c.boundaries (SAP_Install.configuration c).std program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (SAP_Install.configuration c)) prior) := by
  refine ⟨DrvC_SourceEntry.same_program {c with boundaries:=F3M_CircleSource.install c.boundaries} hashv,
    DrvC_Installation.aus1_dictionary (SAP_Install.configuration c),?_,?_⟩
  · exact DrvC_SourceHeadline.deployed_headline_source
      {c with boundaries:=F3M_CircleSource.install c.boundaries} D P Q0 Q1 hqueries hashv runtime raw binding
      adversary chooseSecond prefixBound choiceBound project
  · obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
      FJp_Ret_LiteralPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (SAP_Install.configuration c).adapter (SAP_Install.configuration c).currentBase
      (SAP_Install.configuration c).reserved (SAP_Install.configuration c).query
      (SAP_Install.configuration c).geometry (SAP_Install.configuration c).stageBase
      (SAP_Install.configuration c).finish c.boundaries
      (SAP_Install.configuration c).std native1 native2 primitiveOwner hashv extraction
      prior sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 Par_Parameters.deployed root length words
    have ⟨cuts,writer,reader,multiproof,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
    have sourceFacts := T2R_Parser.on_run _ _ _ _ _ _ _ _ _ _ _ _ _ run header1.2.2.1 scanned.2.2
    refine ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,sourceFacts,?_,caller⟩
    exact T2R_Nonvacuity.same_cuts L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      {c with boundaries:=F3M_CircleSource.install c.boundaries} native1 native2
      (SAP_Binding.prepare c) primitiveOwner hashv extraction sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
      f s cuts writer reader

#print axioms deployed
end AspisR1.FJp_Ret_LiteralTop
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJp_Ret_R3Top
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
    (FJp_Ret_R3Result.Outcome L e1 e2 w1 w2 (Rc3_Install.configuration c reservation).adapter (Rc3_Install.configuration c reservation).currentBase (Rc3_Install.configuration c reservation).reserved (Rc3_Install.configuration c reservation).query (Rc3_Install.configuration c reservation).geometry (Rc3_Install.configuration c reservation).stageBase (Rc3_Install.configuration c reservation).finish c.boundaries reservation program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (Rc3_Install.configuration c reservation)) prior) ∧
    (native1 program e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (Rc3_Install.configuration c reservation) hashv native1 native2 copy allocator program H saved ∧
    Rc2_Protection.Facts (Rc3_Install.configuration c reservation) native1 native2 copy allocator program := by
  obtain ⟨driverEq,sdkEq,headline,original⟩ := FJp_Ret_LiteralTop.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 (Rc2_Install.select c reservation) native1 native2
    primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project words
  refine ⟨driverEq,sdkEq,headline,?_,?_,?_,?_⟩
  · obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,parser,acceptance,caller⟩ := original
    have cuts := base.1
    have strong := Rc2_Base.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ _ reservation program
      data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run base
    have initial := NP6_Constructors.on_run _ _ _ _ _ _ _ _ _ _ _ run
    exact ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,strong,initial,selected,publicFacts,parser,acceptance,
      Rc3_Nonvacuity.derive _ _ _ _ _ _ _ _ acceptance,caller⟩
  · exact PoolT_Write.accepted_verifier_writes_copy _ native1 native2 hashv extraction copy std allocator
      e1 program data1 state1 final1 saved post1 accepted1
  · exact Rc2_Events.derive _ hashv native1 native2 extraction copy allocator program sha256 H p1 syscall saved
  · exact Rc2_Protection.derive _ hashv native1 native2 extraction copy std allocator program

#print axioms deployed
end AspisR1.FJp_Ret_R3Top
end
