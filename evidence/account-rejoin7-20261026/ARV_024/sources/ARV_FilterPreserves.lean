import ARV_Filter
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterPreserves
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

theorem supported
    (H : Bytes → State)
    (n : ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) :
    eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      eval H (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  have eligible : ARV_ObservedSupport.Eligible (Tx := Tx) L copy allocator c err r native1 native2 hashv a
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)) :=
    ⟨H,rfl,⟨n⟩⟩
  rw [ARV_Filter.eval_runtime,ART_Runtime.eval_runtime]
  simp only [if_pos (Or.inr eligible)]

theorem rejected (H : Bytes → State)
    (no : SCE_Experiment.accepted (eval H (ART_PartialAccount.account (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = false) :
    eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      eval H (ART_Runtime.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  rw [ARV_Filter.eval_runtime,ART_Runtime.eval_runtime]
  simp only [if_pos (Or.inl no)]

#print axioms supported
#print axioms rejected
end AspisR1.ARV_FilterPreserves
end
