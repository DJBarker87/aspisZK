import NNC_ActualChoices
import NNC_NoSecondCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNC_ActualObservation
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment FS FS2
open AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable

/-- The output measured by the averaging fold is exactly the two eval-selected
inputs and the same first reply. Rejected first phases are also retained. -/
theorem output {A : Type} (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (a : Adversary A) (H : Bytes → State) :
    (eval H (NNC_ActualChoices.program native1 copy allocator a)).2 =
      let i := NNC_ActualChoices.first a H
      match S2W_D189Wrappers.first native1 copy allocator i.entry CPH_Program.verifier i.data i.state with
      | .ok (.Ok (saved,post,final)) =>
        (i, some (saved,post,final,NNC_ActualChoices.second a H saved post final))
      | _ => (i,none) := by
  unfold NNC_ActualChoices.program NNC_ActualChoices.first NNC_ActualChoices.second
  simp only [eval_bind]
  split <;> simp_all only [eval_bind,eval,List.append_nil,NNC_ActualChoices.first]

/-- No attack outcome is erased by the inherited runtime's support test:
the full attack probability is bounded by the measured max, for ANY attack
predicate. There is no admission or Realizes restriction on this predicate. -/
theorem attack_mass_le {A B C : Type}
    (execution : Program Bytes State A) (runtime : Program Bytes State B)
    (model : Program Bytes State C) (mass : View Bytes State B → Rat)
    (attack : View Bytes State A → Prop) :
    lazyMean execution emptyTable (fun v => indicator (attack v)) ≤
      lazyMean (F3U_Joint.program runtime execution model) emptyTable
        (fun v => max (mass v.2.1) (indicator (attack v.2.2.1))) := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  rw [F3U_Joint.output]
  exact le_max_right _ _

#print axioms output
#print axioms attack_mass_le
end AspisR1.NNC_ActualObservation
end
