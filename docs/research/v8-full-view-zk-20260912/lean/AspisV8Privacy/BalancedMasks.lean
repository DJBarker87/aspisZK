import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM. Explicit parametrization of ONE sum-zero
constraint. Option.none is the dependent coordinate; some i are independent.
Source mapping of active/inactive rows belongs to the separate adapter. -/
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Privacy
noncomputable section
variable {I F : Type*} [Fintype I] [AddCommGroup F]

def balanceConstraint (t : Option I → F) : F := t none + ∑ i, t (some i)

def balancedTable (r : I → F) : Option I → F
  | none => -(∑ i, r i)
  | some i => r i

theorem balanced_constraint (r : I → F) : balanceConstraint (balancedTable r) = 0 := by
  simp [balanceConstraint, balancedTable]

theorem balanced_injective : Function.Injective (balancedTable : (I → F) → Option I → F) := by
  intro a b h
  funext i
  exact congrFun h (some i)

/-- Every constrained table has exactly one free-coordinate preimage.
Together with finite uniform coins, this proves uniformity on the hyperplane. -/
def balancedEquiv : (I → F) ≃ {t : Option I → F // balanceConstraint t = 0} where
  toFun r := ⟨balancedTable r, balanced_constraint r⟩
  invFun t := fun i => t.val (some i)
  left_inv r := by rfl
  right_inv t := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
        have h := t.property
        change t.val none + ∑ j, t.val (some j) = 0 at h
        change -(∑ j, t.val (some j)) = t.val none
        have shifted := congrArg (fun x : F => x - ∑ j, t.val (some j)) h
        simpa using shifted.symm
    | some i => rfl

theorem balanced_add (a b : I → F) :
    balancedTable (fun i => a i + b i) = fun i => balancedTable a i + balancedTable b i := by
  funext i
  cases i with
  | none => simp [balancedTable, Finset.sum_add_distrib, neg_add_rev, add_comm]
  | some i => rfl

/-- Adding any number of independent active coordinates does not create
another inactive degree of freedom. A product coin-space adapter is enough. -/
def activeAndBalanced {A : Type*} (active : A → F) (inactive : I → F) :
    (A → F) × (Option I → F) := (active, balancedTable inactive)

#print axioms balanced_constraint
#print axioms balanced_injective
#print axioms balancedEquiv
#print axioms balanced_add
end
end AspisV8Privacy
