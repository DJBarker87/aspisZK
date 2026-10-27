import R1Z.PV_Inv_Guard
import Mathlib.Data.List.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_ConstantTrace
variable {K : Type} [Field K] [DecidableEq K]

def zeroBranches (xs : List K) : List Bool := xs.map (fun x => decide (x=0))

theorem all_false (xs : List K) (h : ∀ x ∈ xs, x ≠ 0) :
    zeroBranches xs=List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs, y ≠ 0 := fun y hy => h y (by simp [hy])
    change decide (x=0) :: zeroBranches xs = List.replicate (xs.length+1) false
    rw [ih hxs]
    simp [hx,List.replicate_succ]

theorem same_schedule (xs ys : List K) (hx : ∀ x ∈ xs, x ≠ 0) (hy : ∀ y ∈ ys, y ≠ 0)
    (hlen : xs.length=ys.length) : zeroBranches xs=zeroBranches ys := by
  rw [all_false xs hx,all_false ys hy,hlen]

#print axioms all_false
#print axioms same_schedule
end R1Z.PV_Inv_ConstantTrace
