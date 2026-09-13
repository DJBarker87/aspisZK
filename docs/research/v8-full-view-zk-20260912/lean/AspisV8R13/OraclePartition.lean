import Mathlib.Logic.Equiv.Defs

/-! Factoring a single function over a disjoint input partition is an exact
bijection, not an additional assumption of independent random oracles. -/
set_option autoImplicit false
namespace AspisV8R13
variable {A B O X Y Digest : Type*}

def splitOracle : ((A ⊕ B) → Digest) ≃ ((A → Digest) × (B → Digest)) where
  toFun H := (fun a => H (Sum.inl a), fun b => H (Sum.inr b))
  invFun pair := fun key => match key with
    | Sum.inl a => pair.1 a
    | Sum.inr b => pair.2 b
  left_inv H := by funext key; cases key <;> rfl
  right_inv pair := by cases pair; rfl

def reindexOracle (e : A ≃ B) : (A → Digest) ≃ (B → Digest) where
  toFun H := fun b => H (e.symm b)
  invFun H := fun a => H (e a)
  left_inv H := by funext a; simp
  right_inv H := by funext b; simp

/-- The unchanged context may select the address partition, roots and coin
bijection. It cannot be recomputed from cells subsequently moved. -/
def preserveContext (e : O → X ≃ Y) : (O × X) ≃ (O × Y) where
  toFun pair := (pair.1, e pair.1 pair.2)
  invFun pair := (pair.1, (e pair.1).symm pair.2)
  left_inv pair := by cases pair; simp
  right_inv pair := by cases pair; simp

#print axioms splitOracle
#print axioms reindexOracle
#print axioms preserveContext
end AspisV8R13
