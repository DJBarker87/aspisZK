/- New-prefix accepted-only consumer; source of origin: lean/SAP_DirectPair.lean. -/
import SAF_C_SAP_ClosedPair
import SAF_C_SAP_DirectConsumer
import SAF_C_SAP_DirectResult
import SAF_C_SAP_ActualPair
import SAF_C_SAP_CloseConsumer
import SAF_C_SAP_ClosedResult
import SAF_C_SAP_PairSelected
import SAF_C_SAP_ActualResult
import SAF_C_SAP_SourceConsumer
import SAP_PrepareOwner
import SAP_NativePair
import SAF_C_SAP_ResultSelected
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Ten
import SAF_C_Cons_Finish
import Cons_Native
import Cons_Continuation
import Cons_Base
import Cons_Caller
import Cons_Result
import T2R_ResultSource
import SAF_C_T2R_Finish
import Cons_NativeBuild
import SAF_C_Cons_FinishProof
import Cons_Second
import T2Nat_ReaderEffects
import CPhy_Physical
import T2Nat_FinishResult
import CPhy_Header
import CPhy_Ranges
import CPhy_Accepted
import WAdm_NativeEndpoint
import SdkD_Accepted
import SdkD_Inner
import SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.SAF_C_SAP_DirectPair
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
    SAF_C_SAP_DirectResult.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H prior := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,selected,publicFacts,caller⟩ :=
    SAF_C_SAP_ClosedPair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops reserved queryOps geoOps stageBase finishOps B
      claimsStd native1 native2 primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length words
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,selected,publicFacts,?_⟩
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
end AspisR1.SAF_C_SAP_DirectPair
end
