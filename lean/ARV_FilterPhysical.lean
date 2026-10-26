import ARV_Filter
import ART_PhysicalView
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterPhysical
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem observed (H : Bytes → State) (run : F3T_Experiment.RunView)
    (found : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run) :
    F3T_Experiment.view run = ART_PhysicalView.physical (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a H := by
  rw [ARV_Filter.eval_runtime] at found
  dsimp only at found
  split at found
  · rw [←Option.some.inj found]
    rfl
  · cases found

#print axioms observed
end AspisR1.ARV_FilterPhysical
end
