import PV_B3_MaskSparseStates
namespace PV_B3_MaskSparseBound
open Aeneas Aeneas.Std PV_B3_MaskSparseStates
set_option autoImplicit false

def Bound (f : Nat → U8) : Prop := ∀ k, (f k).val ≤ 2

theorem update (f : Nat → U8) (h : Bound f) (key : Nat) (v : U8) (hv : v.val ≤ 2) :
    Bound (Function.update f key v) := by
  intro k
  by_cases hk : k = key
  · subst k
    simpa only [Function.update_self] using hv
  · rw [Function.update_of_ne hk]
    exact h k

#print axioms Bound
#print axioms update
end PV_B3_MaskSparseBound
