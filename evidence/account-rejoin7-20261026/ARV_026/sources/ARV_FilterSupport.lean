import ARV_FilterPreserves
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterSupport
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

theorem accepted
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run)
    (yes : run.2.2 = true) :
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  rw [ARV_Filter.eval_runtime] at observed
  split at observed
  · rename_i keep
    have same := Option.some.inj observed
    have rawYes : SCE_Experiment.accepted (eval H (ART_PartialAccount.account
        (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a)).2 = true := by
      rw [←same] at yes
      exact yes
    rcases keep with rejected | eligible
    · rw [rawYes] at rejected
      cases rejected
    · exact (ARV_ObservedSupport.at_eval L copy allocator c err r native1 native2 hashv a extraction H).mp eligible
  · cases observed

#print axioms accepted
end AspisR1.ARV_FilterSupport
end
