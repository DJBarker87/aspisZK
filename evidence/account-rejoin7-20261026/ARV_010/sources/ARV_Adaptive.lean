import ARV_Freeze
import ART_QueryCylinder
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Adaptive
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

def adversary {A : Type} (i : FirstInputs A) (j : SecondInputs A)
    (address : Bytes) (original : State) : Adversary A :=
  ⟨.done i,fun _ _ _ _ => .ask address fun value =>
    .done (if value = original then j else ARV_Constant.poison j)⟩

theorem no_support {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (i : FirstInputs A) (j : SecondInputs A) (address : Bytes) (original : State)
    (H : Bytes → State) (different : H address ≠ original) :
    ¬ Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv
      (adversary i j address original) H) := by
  rintro ⟨n⟩
  have admission := n.entry.admission2
  simp only [adversary,eval,if_neg different] at admission
  exact ARV_Poison.no_admission L j.entry n.entry.w2 7 admission

#print axioms no_support
end AspisR1.ARV_Adaptive
end
