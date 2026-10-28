import R1Z.PV_RW_NativeForSource
set_option autoImplicit false
namespace R1Z.PV_RW_NativeForBound
open Aeneas Aeneas.Std Result
open PV_RW_NativeForSource

theorem sufficient {S : Type} (step : U32 → S → Result S) (fuel : Nat)
    (values : Slice U32) (i : Nat) (state : S) (bound : values.val.length-i<fuel) :
    run step (⟨values,i⟩ : Iter) state=bounded step fuel (⟨values,i⟩ : Iter) state := by
  induction fuel generalizing i state with
  | zero => omega
  | succ fuel ih =>
    by_cases active : i<values.val.length
    · rw [run_some step values i active,bounded_some step values i active]
      apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
      intro next _
      apply ih
      omega
    · have stopped : values.val.length ≤ i := by omega
      rw [run_none step values i stopped,bounded_none step values i stopped]

theorem exact_fuel {S : Type} (step : U32 → S → Result S)
    (values : Slice U32) (i : Nat) (state : S) :
    run step (⟨values,i⟩ : Iter) state=
      bounded step (values.val.length-i+1) (⟨values,i⟩ : Iter) state :=
  sufficient step _ values i state (by omega)

theorem arity16 {S : Type} (step : U32 → S → Result S)
    (values : Array U32 16#usize) (state : S) :
    run step (⟨Array.to_slice values,0⟩ : Iter) state=
      bounded step 17 (⟨Array.to_slice values,0⟩ : Iter) state := by
  apply sufficient
  have shape : (Array.to_slice values).val.length=16 := values.property
  rw [shape]
  omega
#print axioms sufficient
#print axioms exact_fuel
#print axioms arity16
end R1Z.PV_RW_NativeForBound
