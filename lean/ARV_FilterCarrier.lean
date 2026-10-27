import ARV_FilterPreserves
import ART_Carrier
import ARU_Carrier
import ARV_FilterSupport
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterCarrier
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem projection (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run) :
    run.2.1.stored = (eval H (submission a)).2.stored ∧
    run.2.1.physical.bytes = (eval H (submission a)).2.publicBytes := by
  have original : (eval H (ART_Runtime.runtime (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = some run := by
    rw [ARV_Filter.eval_runtime] at observed
    dsimp only at observed
    split at observed
    · rw [ART_Runtime.eval_runtime]
      exact observed
    · cases observed
  exact ART_Carrier.projection (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a H run original

theorem source_view
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run)
    (yes : run.2.2 = true) :
    eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a) =
      eval H (SCE_Experiment.runtime (FIp_Install.configuration err c r) hashv copy allocator CPH_Program.verifier a) := by
  obtain ⟨n⟩ := ARV_FilterSupport.accepted L copy allocator c err r native1 native2 hashv a extraction H run observed yes
  have same := (ARU_PartialAccepted.accepted L copy allocator c err r native1 native2 hashv extraction a H n).2
  rw [ARV_FilterPreserves.supported L copy allocator c err r native1 native2 hashv a H n,
    ART_Runtime.eval_runtime,SCE_Experiment.runtime_eval,same]

#print axioms projection
#print axioms source_view
end AspisR1.ARV_FilterCarrier
end
