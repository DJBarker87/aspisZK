import NNH_StateNormalize
import NNC_ActualChoices
import NNE_AbortIndicator
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_StateSelect
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment NNH_StateNormalize

theorem first_eq (a : Adversary Bool) (H : Bytes → State) :
 NNC_ActualChoices.first (normalize a) H = firstAt a H :=
 congrArg Prod.snd (first_eval a H)

theorem second_eq (a : Adversary Bool) (H : Bytes → State)
 (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 NNC_ActualChoices.second (normalize a) H saved post final = secondAt a H saved post final := by
 unfold NNC_ActualChoices.second
 rw [first_eq]
 exact congrArg Prod.snd (second_eval a H (firstAt a H) saved post final)

/-- RZ-STATE selector with the actual abort-indicator allocator. The L154
parameter counts the normalised adversary; no query premise on raw a is used.
The accepted1/source/runtime premises are the original headline obligations,
not new hypotheses permitted for the completed G0 assembly. -/
theorem selects {C : Type}
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (base : DrvC_Installation.Configuration FIo_Install.W C)
 (err : C) (reservation : NP6_StdModel.Reservation)
 (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction
  (DrvC_Installation.sdk (FIp_Install.configuration err base reservation)) native1 native2 hashv)
 (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
 (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
 (a : Adversary Bool) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
 (accepted1 : S2W_D189Wrappers.first native1 copy NNE_AbortIndicator.allocator
  (firstAt a H).entry CPH_Program.verifier (firstAt a H).data true = ok (.Ok (saved,post,true)))
 (Q0 Q1 : Nat) (queries : ∀ K,
  (ARW_Induced.issued native1 copy NNE_AbortIndicator.allocator CPH_Program.verifier
   (normalize a) K).length ≤ Q0+Q1) :
 ARQ_Observer.select (FIp_Install.configuration err base reservation) CPH_Program.verifier
  (eval H (ARX_LocalCharge.bounded
   (ART_PartialAccount.account (FIp_Install.configuration err base reservation)
    hashv copy NNE_AbortIndicator.allocator CPH_Program.verifier (normalize a)) (Q0+Q1))).2 =
 P2P_NativeSelection.pair (DrvC_Installation.sdk (FIp_Install.configuration err base reservation))
  CPH_Program.verifier (firstAt a H).entry (secondAt a H saved post true).entry
   (secondAt a H saved post true).data (secondAt a H saved post true).slot := by
 have accepted : S2W_D189Wrappers.first native1 copy NNE_AbortIndicator.allocator
  (NNC_ActualChoices.first (normalize a) H).entry CPH_Program.verifier
  (NNC_ActualChoices.first (normalize a) H).data
  (NNC_ActualChoices.first (normalize a) H).state = ok (.Ok (saved,post,true)) := by
  rw [first_eq]
  exact accepted1
 have h := NNC_ActualChoices.selected copy NNE_AbortIndicator.allocator base err reservation
  native1 native2 hashv extraction sha256 H p1 syscall (normalize a) saved post true
  accepted (Q0+Q1) queries
 simpa only [first_eq,second_eq] using h

#print axioms first_eq
#print axioms second_eq
#print axioms selects
end AspisR1.NNH_StateSelect
