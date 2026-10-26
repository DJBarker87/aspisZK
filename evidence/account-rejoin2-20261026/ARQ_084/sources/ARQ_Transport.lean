import ARQ_RecoveryBranch
import ARQ_ModelAccepted
import ARQ_SourceBranch
import ARQ_SourceAlternative
import ARQ_NativeReplies
import SCG_SharedNative
import ARQ_ByteSourceAccepts
import ARQ_Observer
import Rc9_Top
import ARP_Interface
import FIp_Top
import S6N_Installation
import Rc8_Top
import Rc9_Install
import FIp_Install
import FIp_Core
import FIo_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.ARQ_Join
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

/-- Pointwise direct-account raw join on ALL adversaries/oracles, under the
retained native/game/runtime hypotheses indexed to this world's actual choices.
No source acceptance, StoredCarrierBinding or event transport is assumed.
The all-world representation/support and recovery obligations are separate. -/
theorem accepted_recovery_or_account_collision {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (a : SCE_Experiment.Adversary A) (w1 w2 : W)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (admission1 : RuntimeEntrypointAdmission L (eval H a.first).2.entry w1 3)
    (admission2 : RuntimeEntrypointAdmission L
      (eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry w2 7)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator ((eval H a.first).2.entry) CPH_Program.verifier ((eval H a.first).2.data) ((eval H a.first).2.state) =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) CPH_Program.verifier ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.data) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.slot) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.state) =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u ((eval H a.first).2.entry) ((eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry) saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder)
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    :
    let r := FIp_Install.configuration indexError c reservation
    SCE_Experiment.accepted (eval H (SCE_Experiment.account r hashv copy allocator CPH_Program.verifier a)).2 = true →
    eval H (F3T_Installed.source r hashv (input r (eval H (SCE_Experiment.submission a)).2)) =
      eval H (F3_Model.verifier D (input r (eval H (SCE_Experiment.submission a)).2)) ∧
    (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift r (SCE_Experiment.submission a))))).2.2 = true ∧
    OraclePortRefineJoin.RecoveredInputAgreement
      (ARQ_AccountView.physical r hashv copy allocator CPH_Program.verifier a H)
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift r (SCE_Experiment.submission a))))) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program
        (SCE_Experiment.account r hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select r CPH_Program.verifier))) := by
  dsimp only
  intro accountAccepted
  have source := ARQ_SourceAlternative.accepted L sdk copy std allocator a w1 w2 c indexError reservation
    native1 native2 hashv extraction sha256 H p1 syscall final1 final2 saved post1 post2 admission1 admission2
    accepted1 accepted2 root length prior words p t u actions game RuntimePersistence Q0 Q1 prefixBound choiceBound
  rcases source with sourceAccepted | bad
  · have branch := ARQ_RecoveryBranch.accepted
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation)
      (FIo_Install.finishOps reservation c.finish)
      (FIo_Nonvacuity.arithmetic_fixed reservation c.finish).symm ⟨rfl,rfl,rfl⟩
      hashv D words copy allocator CPH_Program.verifier a Q0 Q1 prefixBound choiceBound
      (F3Y_InstalledLaws.prepare indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.primitives indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.canonical indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.domain indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.multiply indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.one indexError (FIp_Install.select reservation c) reservation)
      (F3Y_InstalledLaws.inverse indexError (FIp_Install.select reservation c) reservation)
      finishOwners (ARQ_Installation.dictionary indexError c reservation) H accountAccepted sourceAccepted
    rcases branch with ⟨raw,agreement⟩ | collision
    · exact Or.inl ⟨raw,ARQ_ModelAccepted.projected D _ H
        (ARQ_ModelAccepted.original _ D hashv (SCE_Experiment.submission a) H sourceAccepted raw),agreement⟩
    · exact Or.inr collision
  · exact Or.inr bad

#print axioms accepted_recovery_or_account_collision
#check @Rc9_Top.deployed
end AspisR1.ARQ_Join
end
