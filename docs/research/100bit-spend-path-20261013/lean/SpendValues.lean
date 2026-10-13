import R0P.PositivityChain
import R0P.Asset

/-! Reuse of the production value rows and copy registry. The three bounded
natural values balance as integers because their possible sum is below the
characteristic. This does not assume the research-only positive family and
does not claim either output value is strictly positive. -/
set_option autoImplicit false

namespace AspisR1.SpendValues

open R0P

variable {K : Type} [Field K]

def BoundedBalanced (A : Trace K) : Prop :=
  ∃ v0 v1 v2 : Nat,
    v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧
    v0 = v1 + v2 ∧
    A 10 1008 = (v0 : K) ∧ A 10 1010 = (v1 : K) ∧ A 10 1012 = (v2 : K)

theorem of_value_balance (prime : Nat) [CharP K prime]
    (hprime : prime = 2 ^ 31 - 1) (pub : Public K) (A : Trace K)
    (hv : Holds valueFamily pub A) (hb : CopyLinkBalance pub A) :
    BoundedBalanced A := by
  obtain ⟨_, hcons0, hcons1⟩ := (value_holds_iff pub A).mp hv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := positivity_copy_cells pub A hb
  obtain ⟨v0, hv0, e0⟩ := valueRow_nat A 1008
    (valueRow_of_holds pub A hv 1008 (Or.inl rfl))
  obtain ⟨v1, hv1, e1⟩ := valueRow_nat A 1010
    (valueRow_of_holds pub A hv 1010 (Or.inr (Or.inl rfl)))
  obtain ⟨v2, hv2, e2⟩ := valueRow_nat A 1012
    (valueRow_of_holds pub A hv 1012 (Or.inr (Or.inr rfl)))
  have a0 : A 0 1014 = (v0 : K) := hc0.symm.trans e0
  have a1 : A 1 1014 = (v1 : K) := hc1.symm.trans e1
  have a2 : A 1 1015 = (v2 : K) := hc2.symm.trans e2
  have hfield : ((v0 : Nat) : K) = ((v1 + v2 : Nat) : K) := by
    push_cast
    rw [← a0, ← a1, ← a2, hcons0, hc3, hcons1]
  have hmod := (CharP.natCast_eq_natCast K prime).mp hfield
  have hbalance : v0 = v1 + v2 := by
    subst hprime
    exact Nat.ModEq.eq_of_lt_of_lt hmod (by omega) (by omega)
  exact ⟨v0, v1, v2, hv0, hv1, hv2, hbalance, e0, e1, e2⟩

#print axioms of_value_balance

end AspisR1.SpendValues
