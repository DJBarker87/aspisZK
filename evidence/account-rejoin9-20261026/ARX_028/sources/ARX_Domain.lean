import ARX_AdmittedRuntime
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARX_Domain
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)


variable (extraction : S2W_DigestExtraction.AeneasExtraction
    (DrvC_Installation.sdk (FIp_Install.configuration err c r)) native1 native2 hashv)
include extraction

theorem range (H : Bytes → State) :
    (∃ run, (eval H (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator c err r native1 native2 hashv a)).2 = some run) ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H) := by
  rw [ARX_AdmittedRuntime.evaluation L copy allocator c err r native1 native2 hashv a extraction H,
    ART_Runtime.eval_runtime]
  dsimp only
  by_cases yes : Nonempty (ARU_Support.At (Tx := Tx) L copy allocator c err r native1 native2 hashv a H)
  · simp only [if_pos yes,exists_eq',iff_true]; exact yes
  · simp only [if_neg yes,reduceCtorEq,exists_false, false_iff]; exact yes

#print axioms range
end AspisR1.ARX_Domain
end
