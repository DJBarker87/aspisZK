/- FIs same-run enrichment; read-only source: P2P_ClosedResult.lean. -/
import RPz7_FIs_Native
import P2P_Origin
/- New-prefix accepted-only consumer; source of origin: lean/SAP_ClosedResult.lean. -/
import RPz7_SAF_C_SAP_ClosedCaller
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_T2R_Ten
import RPz7_SAF_C_T2R_Finish
import RPz7_Cons_Native
import RPz7_SAF_C_T2R_ContSource
import RPz7_Cons_Base
import RPz7_SAF_C_T2R_CallerSource
import RPz7_T2R_PublicDecode
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
namespace AspisR1.FIs_P2P_ClosedResult
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
    (H : Bytes → State)
    (prior : Program Bytes State Unit) : Prop :=
    let port := SdkD_Child.port adapterOps (Uni_Install.current ops reserved queryOps geoOps) (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps (F3M_CircleSource.install B) claimsStd
    ∃ (f : FirstCut) (s : SecondCut), ∃ outer pre middle fs ss,
      ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
        reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
        (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ tx2 : Cons_Native.Witness,
      P2P_Origin.Fact (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) program (e2.second secondSizes) data2 slot s ∧
      FIs_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd)) () s.pub s.proof s.checkpoint tx2 ∧
      Cons_Base.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps (F3M_CircleSource.install B) claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement=ok f.semantic ∧
      T2R_Public.Facts f.pub f.proof ∧
      SAF_C_SAP_ClosedCaller.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B claimsStd program data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run prior tx2
end AspisR1.FIs_P2P_ClosedResult
end
