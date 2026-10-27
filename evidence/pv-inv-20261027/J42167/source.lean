import R1Z.PV_Inv_ConstantTrace
set_option autoImplicit false
namespace R1Z.PV_Inv_OperandPrefix
open PV_Inv_ConstantTrace
variable {K : Type} [Field K] [DecidableEq K]

theorem take_nonzero (xs : List K) (h : ∀ x ∈ xs, x ≠ 0) (n : Nat) :
    ∀ x ∈ xs.take n, x ≠ 0 := fun x hx => h x (List.mem_of_mem_take hx)

theorem stopped_prefix (xs : List K) (h : ∀ x ∈ xs, x ≠ 0) (n : Nat) :
    zeroBranches (xs.take n)=List.replicate (xs.take n).length false :=
  all_false _ (take_nonzero xs h n)

theorem append_safe (xs ys : List K) (hx : ∀ x ∈ xs, x ≠ 0) (hy : ∀ y ∈ ys, y ≠ 0) :
    ∀ x ∈ xs++ys, x ≠ 0 := by
  intro x h
  exact (List.mem_append.mp h).elim (hx x) (hy x)

#print axioms take_nonzero
#print axioms stopped_prefix
#print axioms append_safe
end R1Z.PV_Inv_OperandPrefix
