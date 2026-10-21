import S7OwnedP6RowContract
import S7OwnedP6LoopSimulation

/-! Instantiates the finite-loop induction with the checked four-lane fusion.
No source/reference step-equality premise remains in this symbolic row model.
The Rust Vec/word representation binding is still the external P6 join. -/
set_option autoImplicit false
namespace S7Kani2RowSweep
open S7OwnedP6RowContract S7OwnedP6LoopSimulation
abbrev Rows := Nat → Row

def sourceStep (power : Row) (basis : Nat → Nat) (terms : Nat)
    (i : Nat) (rows : Rows) : Rows :=
  Function.update rows i (source (rows i) power (basis i) (decide (terms%4=3)))

def referenceStep (power : Row) (basis : Nat → Nat) (terms : Nat)
    (i : Nat) (rows : Rows) : Rows :=
  Function.update rows i (fun lane =>
    AspisR1BatchedFoldSourceStep.sourcePush terms (rows i lane) (power lane*basis i))

theorem row_step_refines (power : Row) (basis : Nat → Nat) (terms i : Nat)
    (rows : Rows) : sourceStep power basis terms i rows =
      referenceStep power basis terms i rows := by
  simp only [sourceStep,referenceStep,source_eq_batched_model]

/-- The complete row sweep uses proved row fusion, for every finite width;
64 is the production instantiation. No per-step correspondence is assumed. -/
theorem source_sweep_refines (power : Row) (basis : Nat → Nat) (terms start count : Nat)
    (rows : Rows) :
    run (sourceStep power basis terms) count start rows =
      run (referenceStep power basis terms) count start rows := by
  apply simulation _ _ (fun _ a b => a=b) start count rows rows rfl
  intro i _ _ a b hab
  rw [hab]
  exact row_step_refines power basis terms i b

#print axioms row_step_refines
#print axioms source_sweep_refines
end S7Kani2RowSweep
