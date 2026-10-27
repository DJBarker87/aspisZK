import RPt_FJp_MatchingLaw
import RPz8_ART_PhysicalView
import RPz8_ARX_SourceAlternative
import RPt_FJp_RecoveryBranch
import RPz8_ARQ_ModelAccepted
import RPz8_ARQ_Installation
import RPz8_FIo_Nonvacuity
import RPz8_F3Y_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJp_AccountJoin
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_NativeConsolidation
open F3T_ByteCarrier F3T_Experiment

theorem accepted {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (std : S2W_TrustedStd.TrustedStd copy) (D : LiteralByteProtocol.Decoder)
    (words : CanonicalCutEnrichedTranscript.Words)
    (owners : FJp_GlobalOwners.Owners (FIp_Install.configuration err c r)
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r).boundaries)
    (Q : Nat) (bound : ART_AdversaryWork.work (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a H ≤ Q) :
    (eval H (F3T_Installed.source (FIp_Install.configuration err c r) hashv
      (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) =
        eval H (F3_Model.verifier D (input (FIp_Install.configuration err c r) (eval H (submission a)).2)) ∧
      (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a))))).2.2 = true ∧
      OraclePortRefineJoin.RecoveredInputAgreement
        (ART_PhysicalView.physical (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H)
        (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift (FIp_Install.configuration err c r) (submission a)))))) ∨
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program
        (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)
        ARQ_Observer.project (ARQ_Observer.select (FIp_Install.configuration err c r) CPH_Program.verifier))) := by
  have represented :=  ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a H n
  have replies := ARU_Replies.accepted L copy allocator c err r native1 native2 hashv extraction a H n
  have source := ARX_SourceAlternative.accepted L copy allocator c err r native1 native2 hashv extraction a H n std Q bound
  rcases source with sourceAccepted | bad
  · have branch := FJp_RecoveryBranch.accepted
      (Rc2_Install.configuration (Rc5_Install.seed err (FIp_Install.select r c)) r)
      (FIo_Install.finishOps r c.finish) (FIo_Nonvacuity.arithmetic_fixed r c.finish).symm ⟨rfl,rfl,rfl⟩
      hashv D words copy allocator CPH_Program.verifier a Q H bound
      (F3Y_InstalledLaws.prepare err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.primitives err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.canonical err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.domain err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.multiply err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.one err (FIp_Install.select r c) r)
      (F3Y_InstalledLaws.inverse err (FIp_Install.select r c) r)
      owners (FJp_MatchingLaw.value err c r _) (ARQ_Installation.dictionary err c r) represented.2 replies.2.2 sourceAccepted
    rcases branch with ⟨raw,agreement⟩ | collision
    · apply Or.inl
      have physical := ART_PhysicalView.accepted (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H represented.1
      exact ⟨raw,ARQ_ModelAccepted.projected D _ H
        (ARQ_ModelAccepted.original _ D hashv (submission a) H sourceAccepted raw),by rw [physical]; exact agreement⟩
    · exact Or.inr collision
  · exact Or.inr bad

#print axioms accepted
end AspisR1.FJp_AccountJoin
end
