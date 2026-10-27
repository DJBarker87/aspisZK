import RPz8_SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Projection
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier SCE_Experiment

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

/-- The shared-adversary association is now a projection theorem. Neither
admission nor an additional input equality is assumed. -/
theorem input_projection (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.1 = (eval H (F3T_Canon.canon (lift c (submission a)))).2 := by
  rw [runtime_eval] at observed
  have same := Option.some.inj observed
  rw [← same,F3T_Canon.canon_eval,lift_eval,submission_eval,first_projection]

theorem stored (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.1.stored = (eval H (submission a)).2.stored := by
  rw [input_projection c hashv copy allocator id a H run observed]
  exact SCD_Carrier.canonical_stored c (submission a) H

theorem byte_observation :
    SCD_Carrier.ByteObservation (submission a) (runtime c hashv copy allocator id a) := by
  intro H run observed _
  exact stored c hashv copy allocator id a H run observed

theorem chronological (run : RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.1 = (eval H (account c hashv copy allocator id a)).1 := by
  rw [runtime_eval] at observed
  exact (congrArg Prod.fst (Option.some.inj observed)).symm

#print axioms input_projection
#print axioms stored
#print axioms byte_observation
#print axioms chronological
end AspisR1.SCE_Projection
end
