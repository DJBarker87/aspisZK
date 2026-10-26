import ARV_FilterSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterExact
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem omitted_iff
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) :
    (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = none ↔
    SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = true ∧
    ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  rw [ARV_Filter.eval_runtime]
  dsimp only
  rw [ARV_ObservedSupport.at_eval L copy allocator c err r native1 native2 hashv a extraction H]
  split
  · rename_i kept
    constructor
    · intro impossible; cases impossible
    · rintro ⟨yes,no⟩
      rcases kept with rejected | support
      · rw [yes] at rejected; cases rejected
      · exact False.elim (no support)
  · rename_i dropped
    constructor
    · intro _
      constructor
      · cases yes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account
          (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 with
        | false => exact False.elim (dropped (Or.inl yes))
        | true => rfl
      · exact fun support => dropped (Or.inr support)
    · intro _; rfl

#print axioms omitted_iff
end AspisR1.ARV_FilterExact
end
