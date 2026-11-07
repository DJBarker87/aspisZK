import NNC_RecAccepted
import NNC_ActualChoices
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NNC_ActualAccepted
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

/-- Actual adaptive instantiation of BOTH deployed entries. There is no
free pair and no Realizes premise. This returned-model arm is consumed only
after native Root0/representation assembly, never to infer Root0 itself. -/
theorem actual {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (H : Bytes → State) (a : SCE_Experiment.Adversary A)
    (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record)) (final1 : A)
    (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L (NNC_ActualChoices.first a H).entry w1 3)
    (admission2 : RuntimeEntrypointAdmission L (NNC_ActualChoices.second a H saved post1 final1).entry w2 7)
    (missing : Uninstalled CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) native1 native2 hashv)
    (sha256 : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (final2 : A)
    (post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator (NNC_ActualChoices.first a H).entry CPH_Program.verifier (NNC_ActualChoices.first a H).data (NNC_ActualChoices.first a H).state =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator (NNC_ActualChoices.second a H saved post1 final1).entry CPH_Program.verifier (NNC_ActualChoices.second a H saved post1 final1).data (NNC_ActualChoices.second a H saved post1 final1).slot (NNC_ActualChoices.second a H saved post1 final1).state =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u (NNC_ActualChoices.first a H).entry (NNC_ActualChoices.second a H saved post1 final1).entry saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    :
    (FJv_DResult.Outcome L (NNC_ActualChoices.first a H).entry (NNC_ActualChoices.second a H saved post1 final1).entry w1 w2
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).currentBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).query
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).geometry (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).stageBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).finish (FIp_Install.boundaries (deployedConfiguration missing indexError reservation).boundaries)
      reservation CPH_Program.verifier (NNC_ActualChoices.first a H).data (NNC_ActualChoices.second a H saved post1 final1).data (NNC_ActualChoices.second a H saved post1 final1).slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (ARX_LocalCharge.bounded (ART_PartialAccount.account
            (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)
            hashv copy allocator CPH_Program.verifier a) (Q0+Q1))
          ARQ_Observer.project (ARQ_Observer.select
            (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)
            CPH_Program.verifier))))) := by
  exact NNC_RecAccepted.accepted L sdk copy std allocator
    (NNC_ActualChoices.first a H).entry (NNC_ActualChoices.second a H saved post1 final1).entry w1 w2 admission1 admission2 missing indexError reservation native1 native2 hashv
    extraction sha256 H p1 syscall (NNC_ActualChoices.first a H).data (NNC_ActualChoices.second a H saved post1 final1).data (NNC_ActualChoices.second a H saved post1 final1).slot (NNC_ActualChoices.first a H).state (NNC_ActualChoices.second a H saved post1 final1).state final1 final2
    saved post1 post2 accepted1 accepted2 root length prior words p t u actions game
    RuntimePersistence D a Q0 Q1 queries (NNC_ActualChoices.realizes a H saved post1 final1)

#print axioms actual
end AspisR1.NNC_ActualAccepted
end
