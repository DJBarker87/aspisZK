import R1Z.PV_V263_World
/-! Exact dependent post-world sequencing. This does not assume or prove
native worker adequacy or successful completion of a reached invocation. -/
set_option autoImplicit false
namespace R1Z.PV_V263_Sequential
open Aeneas Aeneas.Std PV_V263_World
open PV_RJ4IDB (NativeEvent)

theorem success {S A B : Type} (first : Q S A) (next : A → Q S B)
    (w : State S) (a : A) (b : B)
    (one : (first w).outcome = .returned (.ok a))
    (two : (next a (first w).state).outcome = .returned (.ok b)) :
    bind first next w =
      ⟨.returned (.ok b),(next a (first w).state).state,
        (first w).events ++ (next a (first w).state).events⟩ := by
  simp only [bind,one,two]

theorem fault {S A B : Type} (first : Q S A) (next : A → Q S B)
    (w : State S) (error : Fault)
    (h : (first w).outcome = .fault error) :
    bind first next w = ⟨.fault error,(first w).state,(first w).events⟩ := by
  simp only [bind,h]

theorem failure {S A B : Type} (first : Q S A) (next : A → Q S B)
    (w : State S) (error : Error)
    (h : (first w).outcome = .returned (.fail error)) :
    bind first next w = ⟨.returned (.fail error),(first w).state,(first w).events⟩ := by
  simp only [bind,h]

theorem divergence {S A B : Type} (first : Q S A) (next : A → Q S B)
    (w : State S) (h : (first w).outcome = .returned .div) :
    bind first next w = ⟨.returned .div,(first w).state,(first w).events⟩ := by
  simp only [bind,h]

/-- All full Result behaviours survive partial projection. A fault/exhaustion
cannot be installed by inventing a source Result, even .div or .fail. -/
theorem no_total_source {S A : Type} (worker : Q S A)
    (w : State S) (error : Fault) (faulted : (worker w).outcome = .fault error) :
    ¬ ∃ source : Result A, ∀ v, sourceProjection (worker v).outcome = some source := by
  rintro ⟨source,h⟩
  have bad := h w
  rw [faulted] at bad
  cases bad

/-- A fixed-world callback reset differs even when both calls return success.
This is a model counterexample to resetting state, not deployed adequacy. -/
def tick : Q Nat Unit := fun w =>
  ⟨.returned (.ok ()),{w with base := w.base + 1},[]⟩

theorem advanced (w : State Nat) :
    (bind tick (fun _ => tick) w).state.base = w.base + 2 := by
  simp only [bind,tick,Nat.add_assoc]

theorem reset_wrong (w : State Nat) :
    (bind tick (fun _ => tick) w).state.base ≠ (tick w).state.base := by
  rw [advanced]
  simp only [tick]
  omega

#print axioms success
#print axioms fault
#print axioms failure
#print axioms divergence
#print axioms no_total_source
#print axioms tick
#print axioms advanced
#print axioms reset_wrong
end R1Z.PV_V263_Sequential
