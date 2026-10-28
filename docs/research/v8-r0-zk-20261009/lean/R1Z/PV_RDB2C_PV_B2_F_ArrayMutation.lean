import R1Z.PV_RDB2C_PV_B2_D_MaterializeTotal
set_option autoImplicit false
namespace PV_B2_F_ArrayMutation
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep
/-- A suffix invariant for the untouched slots of the original zero-filled Vec. -/
def ZeroSuffix (out : Out) (start : Nat) : Prop :=
  ∀ i, start ≤ i → i < 1024 → out.val[i]? = some aspis_core.field.wide_exact.WideExact.ZERO
theorem untouched {α : Type} (xs : List α) (i j : Nat) (x : α) (hne : i ≠ j) :
    (xs.set i x)[j]? = xs[j]? := by
  induction xs generalizing i j with
  | nil => simp
  | cons a xs ih =>
    cases i <;> cases j <;> simp_all [List.set]

theorem update_shape (out out1 : Out) (j : Usize) (x : E)
    (hu : Array.update out j x = ok out1) :
    out1.val = out.val.set j.val x := by
  unfold Array.update at hu
  split at hu
  · cases hu
  · cases Result.ok.inj hu
    rfl

theorem suffix_step (out out1 : Out) (j : Usize) (x : E)
    (hz : ZeroSuffix out j.val) (hu : Array.update out j x = ok out1) :
    ZeroSuffix out1 (j.val+1) := by
  intro i hi hib
  rw [update_shape out out1 j x hu,untouched _ _ _ _ (by omega)]
  exact hz i (by omega) hib
#print axioms untouched
#print axioms update_shape
#print axioms suffix_step
#print Array.update_spec
#print Array.index_usize_spec
#print Array.repeat
end PV_B2_F_ArrayMutation
