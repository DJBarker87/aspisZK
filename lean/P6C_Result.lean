import P6C_FullBoundary
import Rc3_Result
import SAP_LiteralCaller
import Rc3_Nonvacuity
import Rc2_Base
import T2R_Parser
import T2R_Acceptance
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import T2R_Ten
import T2R_Finish
import Cons_Native
import T2R_ContSource
import Cons_Base
import T2R_CallerSource
import T2R_PublicDecode
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
namespace AspisR1.P6C_Result
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

def Outcome {W F CoreError : Type}
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
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)
    ∃ (f : FirstCut) (s : SecondCut), ∃ outer pre middle fs ss,
      ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation))
        reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ tx2 : Cons_Native.Witness,
      Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation))) () s.pub s.proof s.checkpoint tx2 ∧
      Rc2_Base.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps (F3M_CircleSource.install B) reservation program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run ∧
      P6C_OnCuts.SafeBatches (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) hashv H f s ∧
      P6C_FullBoundary.Facts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) hashv H saved f s ∧
      NP6_Constructors.Contents run.initial run.pending ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement=ok f.semantic ∧
      T2R_Public.Facts f.pub f.proof ∧
      T2R_Parser.Facts f.proof ∧
      T2R_Acceptance.Facts driver H f.pub f.proof s.pub s.proof s.checkpoint
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) ∧
      Rc3_Nonvacuity.Facts driver H f.pub f.proof s.pub s.proof s.checkpoint
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) ∧
      SAP_LiteralCaller.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
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
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError)) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (source : Rc3_Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior) :
    Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior hashv := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,initial,selected,publicFacts,
    parser,acceptance,nonvacuity,caller⟩ := source
  have safe := P6C_OnCuts.same_cuts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) native1 native2 hashv extraction
    sha256 H p1 syscall e1.first (e2.second secondSizes) saved f s base.1
  have whole := P6C_FullBoundary.same_cuts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) native1 native2 hashv extraction
    sha256 H p1 syscall e1.first (e2.second secondSizes) saved f s base.1
  exact ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,safe,whole,initial,selected,publicFacts,
    parser,acceptance,nonvacuity,caller⟩

#print axioms strengthen
end AspisR1.P6C_Result
end
