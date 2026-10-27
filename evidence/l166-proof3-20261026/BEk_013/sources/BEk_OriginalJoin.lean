import BEk_OriginalInputs
import ARU_OriginalLaw
import ARU_Join
import ARU_Charges
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_OriginalJoin
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open F3T_ByteCarrier F3T_Experiment
/-- The original partial-account cylinder supplies the existing global join
and charges on the SAME account, adversary, projected event and H. This does
not identify a physical internal batch recorder, or cover every abstract H. -/
theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (native H : Bytes → State)
    (n : ARS_Coverage.SupportedEntry (Tx := Tx) L copy allocator c err r native1 native2 hashv a native)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv native)
    (consistent : ARS_AccountReplay.Consistent
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) native H)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FIp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.Bound (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a Q) :
    eval H (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) =
      eval native (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) ∧
    (∀ (V : Type) (observe : GExq_AccountExperiment.Outcome A → Nat → V),
      observe (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
          hashv copy allocator CPH_Program.verifier a)).2
        (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
          hashv copy allocator CPH_Program.verifier a)).1.length =
      observe (ARS_NativeOutcome.wrappers copy allocator CPH_Program.verifier a native1 native2 native)
        (ARS_NativeAccount.attempts (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a native)) ∧
    (∀ K, FS.firstReads FS.emptyTable (eval K (Hiq_RecordedJoint.program
      (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
      ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))).1 ≤ Q+2965) ∧
    (    (eval H (F3T_Installed.source (FIp_Install.configuration err c r) hashv
      (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) =
        eval H (F3_Model.verifier D (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) ∧
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a))))).2.2 = true ∧
      OraclePortRefineJoin.RecoveredInputAgreement
        (ART_PhysicalView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a)))))) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))) ) := by
  have factory := ARU_OriginalFactory.original L copy allocator c err r native1 native2
    hashv extraction a native H n syscall consistent
  obtain ⟨m⟩ := factory.1
  have law := ARU_OriginalLaw.exact L copy allocator c err r native1 native2 hashv
    extraction a native H n syscall consistent
  have charges := ARU_Charges.charged (FIp_Install.configuration err c r) hashv
    copy allocator CPH_Program.verifier a D Q bound
  exact ⟨factory.2,law.2,charges.1,
    ARU_Join.accepted L copy allocator c err r native1 native2 hashv extraction
      a H m std D words owners Q bound⟩

#print axioms accepted
end AspisR1.BEk_OriginalJoin
end
