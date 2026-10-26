import ARV_FilterCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_FilterCheckpoint
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)

theorem exact
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
    (std : S2W_TrustedStd.TrustedStd copy)
    (H : Bytes → State) (run : F3T_Experiment.RunView)
    (observed : (eval H (ARV_Filter.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run)
    (yes : run.2.2 = true) :
    ∃ saved post final f s,
      (eval H (SCE_Execution.firstCode (FIp_Install.configuration err c r) hashv copy allocator
        CPH_Program.verifier (eval H a.first).2)).2 = ok (.Ok (saved,post,final)) ∧
      S2W_NativeConsolidation.SourceCuts (SCH_IdealSdk.dictionary (FIp_Install.configuration err c r) hashv H)
        (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes) saved f s ∧
      MultiproofConeCanonical.bytesOf s.checkpoint.val = MultiproofConeCanonical.bytesOf saved.val := by
  obtain ⟨n⟩ := ARV_FilterSupport.accepted L copy allocator c err r native1 native2 hashv a extraction H run observed yes
  have same := ARV_FilterCarrier.source_view L copy allocator c err r native1 native2 hashv a extraction H run observed yes
  have source : (eval H (SCE_Experiment.runtime (FIp_Install.configuration err c r)
      hashv copy allocator CPH_Program.verifier a)).2 = some run := by
    rw [←same]
    exact observed
  exact (ARU_Carrier.exact L copy allocator c err r native1 native2 hashv extraction a H n std run source).2.2

#print axioms exact
end AspisR1.ARV_FilterCheckpoint
end
