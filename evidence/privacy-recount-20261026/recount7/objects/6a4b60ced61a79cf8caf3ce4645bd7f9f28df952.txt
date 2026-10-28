import R1Z.PV_RW_IteratorSource
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_NativeForSource
open Aeneas Aeneas.Std Result ControlFlow
abbrev Iter := core.slice.iter.Iter U32

def body {S : Type} (step : U32 → S → Result S) (iterator : Iter) (state : S) :
    Result (ControlFlow (Iter × S) S) := do
  let pair ← PV_RW_IteratorSource.iterator_step.iterator_step iterator
  match pair.1 with
  | none => ok (done state)
  | some value => do
    let next ← step value state
    ok (cont (pair.2,next))

def run {S : Type} (step : U32 → S → Result S) (iterator : Iter) (state : S) : Result S :=
  loop (fun (iterator,state) => body step iterator state) (iterator,state)

def bounded {S : Type} (step : U32 → S → Result S) : Nat → Iter → S → Result S
  | 0, _, _ => .div
  | fuel+1, iterator, state => do
    let flow ← body step iterator state
    match flow with
    | .done out => ok out
    | .cont (nextIterator,nextState) => bounded step fuel nextIterator nextState

theorem body_some {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (state : S) :
    body step (⟨values,i⟩ : Iter) state = (do
      let next ← step values.val[i] state
      ok (cont ((⟨values,i+1⟩ : Iter),next))) := by
  unfold body
  rw [PV_RW_IteratorSource.next_some values i active]
  rfl

theorem body_none {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (stopped : values.val.length ≤ i) (state : S) :
    body step (⟨values,i⟩ : Iter) state=ok (done state) := by
  unfold body
  rw [PV_RW_IteratorSource.next_none values i stopped]
  rfl

theorem run_unfold {S : Type} (step : U32 → S → Result S) (iterator : Iter) (state : S) :
    run step iterator state = (do
      let flow ← body step iterator state
      match flow with
      | .done out => ok out
      | .cont (nextIterator,nextState) => run step nextIterator nextState) := by
  unfold run
  rw [ProverRw19LoopBind.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro flow _
  cases flow with
  | done out => rfl
  | cont pair => rcases pair with ⟨iterator,state⟩; rfl

theorem bounded_some {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (state : S) (fuel : Nat) :
    bounded step (fuel+1) (⟨values,i⟩ : Iter) state = (do
      let next ← step values.val[i] state
      bounded step fuel (⟨values,i+1⟩ : Iter) next) := by
  rw [bounded,body_some step values i active]
  simp only [bind_assoc_eq,bind_tc_ok]

theorem bounded_none {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (stopped : values.val.length ≤ i) (state : S) (fuel : Nat) :
    bounded step (fuel+1) (⟨values,i⟩ : Iter) state=ok state := by
  rw [bounded,body_none step values i stopped]
  rfl

theorem run_some {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (active : i<values.val.length) (state : S) :
    run step (⟨values,i⟩ : Iter) state = (do
      let next ← step values.val[i] state
      run step (⟨values,i+1⟩ : Iter) next) := by
  rw [run_unfold,body_some step values i active]
  simp only [bind_assoc_eq,bind_tc_ok]

theorem run_none {S : Type} (step : U32 → S → Result S) (values : Slice U32) (i : Nat)
    (stopped : values.val.length ≤ i) (state : S) :
    run step (⟨values,i⟩ : Iter) state=ok state := by
  rw [run_unfold,body_none step values i stopped]
  rfl
#print axioms body_some
#print axioms body_none
#print axioms run_unfold
#print axioms bounded_some
#print axioms bounded_none
#print axioms run_some
#print axioms run_none
end R1Z.PV_RW_NativeForSource
