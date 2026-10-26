import ARS_PaddedSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_CostObstruction
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment S2W_D189Consolidation

/-- Conditional refutation of the first-only-to-total-cost inference in the
installed native/game/admission domain. It is not a soundness attack. -/
theorem no_total_budget {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (a : Adversary A) (H : Bytes → State)
    (n : ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
    (Q : Nat) (queries : ∀ K, (eval K (submission a)).1.length ≤ Q) :
    ¬ ∀ b : Adversary A,
      Nonempty (ARQ_WorldSupport.NativeAt (Tx := Tx) L copy allocator c err r native1 native2 hashv b H) →
      (∀ K, (eval K (submission b)).1.length ≤ Q) →
      (eval H (account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier b)).1.length ≤ Q+1921 := by
  intro universal
  obtain ⟨b,_,support,budget,_,cost⟩ := ARS_PaddedSupport.unbounded L copy allocator c err r
    native1 native2 hashv extraction a H n Q queries
  exact (Nat.not_le_of_lt cost) (universal b support budget)

#print axioms no_total_budget
end AspisR1.ARS_CostObstruction
end
