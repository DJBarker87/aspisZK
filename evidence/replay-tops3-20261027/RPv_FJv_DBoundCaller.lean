import RPv_FJv_DCont
import RPz7_PFin_Attach
import RPz7_Rc5_Caller
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_T2R_Ten
import RPz7_T2R_Finish
import RPz7_Cons_Native
import RPz7_T2R_ContSource
import RPz7_T2Nat_ReaderEffects
import RPz7_CPhy_Physical
import T2Nat_FinishResult
import RPz7_SAF_C_SAF_PreparedCaller
import RPz7_CPhy_Header
import RPz7_CPhy_Ranges
import RPz7_CPhy_Accepted
import RPz7_WAdm_NativeEndpoint
import RPz7_SdkD_Accepted
import RPz7_SdkD_Inner
import RPz7_SdkD_Uni
import RPz7_FIs_P2P_Result
import RPz7_P2P_Caller
import RPz7_P2P_Acceptance
import P2P_Origin
import RPz7_P2P_R5Result
import RPz7_Rc5_Result
import RPz7_Rc6_Caller
import RPz7_PFin_Packet
import RPz7_P6C_FullBoundary
import RPz7_CPP_Acceptance
import RPz7_Rc4_Encoding
import RPz7_SAP_PrepareOwner
import RPz7_Rc3_Result
import RPz7_TxS_RawPublic
import RPz7_Rc5_Nonvacuity
import RPz7_Rc2_Base
import RPz7_T2R_Parser
import RPz7_T2R_Acceptance
import RPz7_Cons_Base
import RPz7_T2R_CallerSource
import RPz7_T2R_PublicDecode
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJv_DBoundCaller
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
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State) (f : FirstCut) (s : SecondCut) (outer : S2W_Trace.Log)
    (pre middle : List (S2W_SiteSchedule.Event (Option Unit)))
    (fs : S2W_SiteSchedule.FirstSegments (Option Unit))
    (ss : S2W_SiteSchedule.SecondSegments (Option Unit))
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (prior : Program Bytes State Unit) (tx2 : Cons_Native.Witness) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps (F3M_CircleSource.install B) claimsStd
      let decode := CPhy_Header.decode
      let nodes := CPhy_Ranges.nodes f.proof s.proof
      let y1 := CPhy_Ranges.y1 f.proof
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) ∧
        FJv_DCont.Outcome adapterOps ops stageBase finishOps reserved queryOps geoOps
          B claimsStd prior H f s saved run tx2
end AspisR1.FJv_DBoundCaller
end

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJv_DResult
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
    (prior : Program Bytes State Unit) (events : List S2X.AccountEvent)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) (bad : Prop) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)
    ∃ (f : FirstCut) (s : SecondCut), ∃ outer pre middle fs ss,
      ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation))
        reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ tx2 : Cons_Native.Witness,
      P2P_Origin.Fact (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation)) program (e2.second secondSizes) data2 slot s ∧
      Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation))) () s.pub s.proof s.checkpoint tx2 ∧
      TxS_Encoding.Facts run H ∧
      Rc2_Base.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps (F3M_CircleSource.install B) reservation program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run ∧
      NP6_Constructors.Contents run.initial run.pending ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement=ok f.semantic ∧
      TxS_RawPublic.Facts f.pub f.proof ∧
      T2R_Parser.Facts f.proof ∧
      ∃ version : S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val),
      version.key = (e1.handles 2).1 ∧ version.key = (e2.handles 6).1 ∧
      version.events = events ∧
      bytesOf s.checkpoint.val = payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 ∧
      PFin_Packet.Facts (bytesOf f.pub.val) (bytesOf f.proof.val) (Tx1Q_Carriers.prepared run.p) H ∧
      P6C_OnCuts.SafeBatches (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) hashv H f s ∧
      P6C_FullBoundary.Facts (⟨adapterOps,ops,stageBase,finishOps,reserved,queryOps,geoOps,F3M_CircleSource.install B,NP6_StdModel.calls reservation⟩ : DrvC_Installation.Configuration F CoreError) hashv H saved f s ∧
      (bad ∨
      P2P_Acceptance.Facts driver H f.pub f.proof s.pub s.proof s.checkpoint
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) ∧
      P2P_Acceptance.Nonrejecting driver H f.pub f.proof ∧
      FJv_DBoundCaller.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2)
end AspisR1.FJv_DResult
end
