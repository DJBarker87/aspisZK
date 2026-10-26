/- FIs same-run enrichment; read-only source: P2P_PairSelected.lean. -/
import P2P_Origin
import RPz7_P2P_NativePair
import RPz7_FIs_P2P_ResultSelected
/- New-prefix accepted-only consumer; source of origin: lean/SAP_PairSelected.lean. -/
import RPz7_SAP_NativePair
import RPz7_SAF_C_SAP_ResultSelected
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_Cons_Ten
import RPz7_SAF_C_Cons_Finish
import RPz7_Cons_Native
import RPz7_Cons_Continuation
import RPz7_Cons_Base
import RPz7_Cons_Caller
import RPz7_Cons_Result
import RPz7_T2R_ResultSource
import RPz7_SAF_C_T2R_Finish
import RPz7_Cons_NativeBuild
import RPz7_SAF_C_Cons_FinishProof
import RPz7_FIs_Cons_Second
import RPz7_T2Nat_ReaderEffects
import RPz7_CPhy_Physical
import T2Nat_FinishResult
import RPz7_CPhy_Header
import RPz7_CPhy_Ranges
import RPz7_CPhy_Accepted
import RPz7_WAdm_NativeEndpoint
import RPz7_SdkD_Accepted
import RPz7_SdkD_Inner
import RPz7_SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FIs_P2P_PairSelected
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
    FIs_P2P_ResultSelected.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  unfold FIs_P2P_ResultSelected.Outcome
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
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2run,origin,enriched,?_,selected,?_⟩
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
end AspisR1.FIs_P2P_PairSelected
end
