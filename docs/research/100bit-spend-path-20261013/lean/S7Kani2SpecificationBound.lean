import Lean.Elab.Tactic.Omega

/-! The Kani specification uses a total machine-word sum. The source retains
checked addition; its guard makes that total specification identical to the
natural-number model. No wrapping source operation is introduced. -/
set_option autoImplicit false
namespace S7Kani2SpecificationBound

theorem total_spec_eq_checked_sum (raw product : Nat)
    (hp : product<2^64) (guard : raw≤2^64-1-product) :
    raw+product<2^64 ∧ (raw+product)%2^64=raw+product := by
  have hsum : raw+product<2^64 := by omega
  exact ⟨hsum,Nat.mod_eq_of_lt hsum⟩

#print axioms total_spec_eq_checked_sum
end S7Kani2SpecificationBound
