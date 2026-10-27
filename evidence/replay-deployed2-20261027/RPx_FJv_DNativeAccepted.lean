import RPx_FJv_DFinalSource
import RPx_FJv_DR5Close
import RPx_FJv_DR6Result
import RPx_FJv_DRelease
import RPx_FJt_GlobalTerminal
import RPv_IDa_Deployed
import RPu_FIq_Install
import RPz7_S1SemanticRootCopyV1
import RPz8_ARW_Induced
import RPz8_ARX_Residual
import RPz8_ARW_Observations
import RPz8_Rc10_Top
import RPz8_ART_Runtime
import RPz8_FIs_Top
import RPz8_Rc9_Top
import RPz8_S6N_Installation
import RPz8_Rc8_Top
import RPz8_Rc9_Install
import RPz7_FIp_Install
import RPz8_FIp_Core
import RPz8_FIo_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.FJv_DNativeAccepted
open IDa_Deployed
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open FS FS2
open AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawExtractorCostComposedV2
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

theorem accepted {W A CoreError Tx : Type}
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
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    :
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator (deployedConfiguration missing indexError reservation) indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    (FJv_DResult.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).currentBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).query
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).geometry (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).stageBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).finish (FIp_Install.boundaries (deployedConfiguration missing indexError reservation).boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv P)
          F3X_Projection.project select)))) := by
  let c:=FJt_GlobalTerminal.configuration missing indexError reservation
  have original:=FJv_DFinalSource.source (Tx:=Tx) L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    missing indexError reservation native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior words
  have closed:=FJv_DR5Close.from_saf L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    (FIp_Install.select reservation (IDa_Deployed.deployedConfiguration missing indexError reservation))
    indexError reservation native1 native2 hashv extraction sha256 H p1 syscall CPH_Program.verifier
    data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    p t u actions game (Hist_Nonvacuity.key 0#u8) CPH_Program.not_system RuntimePersistence original
  have enriched:=FJv_DR6Result.strengthen L e1 e2 w1 w2 c.adapter c.currentBase c.reserved c.query c.geometry
    c.stageBase c.finish (IDa_Deployed.boundaries reservation) reservation CPH_Program.verifier
    data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver c) prior (p.physicalEvents t)
    hashv native1 native2 extraction sha256 p1 syscall closed
  let P:=ARW_Induced.program native1 copy allocator CPH_Program.verifier a
  have queryBound : ∀ H, (eval H P).1.length≤Q0+Q1 := by
    intro H
    rw [ARW_Induced.queries]
    exact queries H
  have budget:=F3Y_AccountMass.budget
    (Rc2_Install.configuration (Rc5_Install.seed indexError
      (FIp_Install.select reservation (IDa_Deployed.deployedConfiguration missing indexError reservation))) reservation)
    hashv D words P (Q0+Q1) queryBound
  exact FJv_DRelease.remove L e1 e2 w1 w2 c.adapter c.currentBase c.reserved c.query c.geometry
    c.stageBase c.finish (IDa_Deployed.boundaries reservation) reservation CPH_Program.verifier
    data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver c) prior (p.physicalEvents t)
    hashv (F3X_Account.program c hashv P) F3X_Projection.project (Q0+Q1) budget enriched
#print axioms accepted
end AspisR1.FJv_DNativeAccepted
end
