import S8OwnedP6Finish

/-! Explicit finite induction on the *extracted* owned step. No whole-loop
unrolling, no leaf-success premise, and no bound on the raw U64 lanes.
This module does not identify Rust pointers with the Aeneas iterator model. -/
set_option autoImplicit false
noncomputable section
namespace S8Kani2FinishTraversal
open Aeneas Aeneas.Std Result ControlFlow
open S8OwnedP6 S8OwnedP6Finish

abbrev State := Weights × Usize

def step (raw : Raw) (state : State) : Result State := do
  let row ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
    S8OwnedP6ValueModel.Row) raw state.2
  let value ← value_owned row
  let (_,back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
    S8OwnedP6ValueModel.Q) state.1 state.2
  let next ← state.2 + 1#usize
  ok (back value,next)

def steps (raw : Raw) : Nat → State → Result State
  | 0, state => ok state
  | n+1, state => do let next ← step raw state; steps raw n next

/-- One running extracted body is precisely a single reference step. -/
theorem extracted_step (raw : Raw) (state : State)
    (running : state.2 < alloc.vec.Vec.len state.1) :
    finish_owned_loop.body raw state.1 state.2 =
      (do let next ← step raw state; ok (.cont next)) := by
  simp only [finish_owned_loop.body,if_pos running,step,bind_assoc_eq]
  rfl

/-- At exhaustion the actual body returns the current destination. -/
theorem extracted_exit (raw : Raw) (state : State)
    (stop : ¬ state.2 < alloc.vec.Vec.len state.1) :
    finish_owned_loop.body raw state.1 state.2 = .ok (.done state.1) := by
  simp only [finish_owned_loop.body,if_neg stop]

/-- Invariant-preserving local equations compose for every iteration count.
The induction is on n, never on concrete field values or recurrence cells. -/
theorem steps_invariant (raw : Raw) (invariant : State → Prop)
    (preserve : ∀ state, invariant state →
      ∃ next, step raw state=.ok next ∧ invariant next)
    (n : Nat) (state : State) (initial : invariant state) :
    ∃ final, steps raw n state=.ok final ∧ invariant final := by
  induction n generalizing state with
  | zero => exact ⟨state,rfl,initial⟩
  | succ n ih =>
    obtain ⟨next,hs,hinv⟩ := preserve state initial
    obtain ⟨final,hsteps,hfinal⟩ := ih next hinv
    exact ⟨final,by simp only [steps,hs,bind_tc_ok,hsteps],hfinal⟩

#print axioms extracted_step
#print axioms extracted_exit
#print axioms steps_invariant
end S8Kani2FinishTraversal
