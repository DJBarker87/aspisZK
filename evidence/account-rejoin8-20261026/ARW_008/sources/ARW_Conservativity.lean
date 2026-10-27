import ARW_Induced
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARW_Conservativity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
variable {A : Type}
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

/-- With a pure second choice, the induced program is literally the old
submission program, not merely equal in distribution. -/
theorem program_on_old_class
    (choose : FirstInputs A → SecondInputs A)
    (pureChoice : a.second = fun i _ _ _ => .done (choose i)) :
    ARW_Induced.program native1 copy allocator id a = submission a := by
  unfold ARW_Induced.program submission
  congr 1
  funext i
  rw [pureChoice]
  split <;> rfl

theorem queries_on_old_class
    (choose : FirstInputs A → SecondInputs A)
    (pureChoice : a.second = fun i _ _ _ => .done (choose i)) (Q : Nat)
    (old : ∀ H, (eval H (submission a)).1.length ≤ Q) :
    ∀ H, (ARW_Induced.issued native1 copy allocator id a H).length ≤ Q := by
  intro H
  rw [←ARW_Induced.queries,program_on_old_class native1 copy allocator id a choose pureChoice]
  exact old H

#print axioms program_on_old_class
#print axioms queries_on_old_class
end AspisR1.ARW_Conservativity
end
