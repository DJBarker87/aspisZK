import NNC_ActualChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_ActualRecorded
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment

/-- The probability envelope recorder selects EXACTLY the actual adaptive
pair, at every H with the attack antecedent accepted1. There is no Realizes
condition in either the numerical probability space or this theorem. -/
theorem selected_at_recorder {A C : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (a : Adversary A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator
      (NNC_ActualChoices.first a H).entry CPH_Program.verifier (NNC_ActualChoices.first a H).data (NNC_ActualChoices.first a H).state =
        ok (.Ok (saved,post,final)))
    (Q : Nat) (queries : ∀ K,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a K).length ≤ Q) :
    let cfg := FIp_Install.configuration err base reservation
    let capped := ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) Q
    let recorder := Hiq_RecordedJoint.program capped ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
    ARQ_Observer.select cfg CPH_Program.verifier (eval H recorder).2.2 =
      P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier
        (NNC_ActualChoices.first a H).entry (NNC_ActualChoices.second a H saved post final).entry
        (NNC_ActualChoices.second a H saved post final).data (NNC_ActualChoices.second a H saved post final).slot := by
  dsimp only
  rw [Hiq_RecordedJoint.source_view]
  exact NNC_ActualChoices.selected copy allocator base err reservation native1 native2 hashv
    extraction sha256 H p1 syscall a saved post final accepted1 Q queries

#print axioms selected_at_recorder
end AspisR1.NNC_ActualRecorded
