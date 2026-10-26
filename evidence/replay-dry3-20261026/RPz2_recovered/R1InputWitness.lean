import R1InputWitnessCore
import R0P.Extraction

/-! Concrete ownership/nullifier/membership and occupied-pair witnesses,
all read from the same production trace. -/
set_option autoImplicit false
namespace AspisR1.InputWitness
open R0P InputWitnessCore
variable {K : Type} [Field K]

attribute [local irreducible] nodeCompress poseidonPermutation merkleRoot

theorem of_production (pub : Public K) (A : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) :
    Relation pub (A 10 1008) (traceSk A) (traceSalt A) (tracePath A) (InputPair.leaf A) := by
  have hn := input_note_trace_witness pub A h.1.2.2.2.1 h.1.2.2.2.2.1
    h.1.2.2.2.2.2.1 h.1.2.2.1 h.1.2.2.2.2.2.2.1 h.2
  have hp := InputPairSelection.of_production pub A lam chi h
  exact ⟨hp.valid, hp.spendable, hp.selected.trans hn.2.2,
    trace_sibling pub A h.2, hn.1, hn.2.1⟩

/-- The bounded natural values and integer conservation come from the
existing value theorem; the input relation uses that exact natural value. -/
theorem bounded_of_production (prime : Nat) [CharP K prime] (hprime : prime = 2 ^ 31 - 1)
    (pub : Public K) (A : Trace K) (lam chi : K)
    (h : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A) :
    ∃ v0 v1 v2 : Nat,
      v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧ v0 = v1 + v2 ∧
      A 10 1008 = (v0 : K) ∧ A 10 1010 = (v1 : K) ∧ A 10 1012 = (v2 : K) ∧
      Relation pub (v0 : K) (traceSk A) (traceSalt A) (tracePath A) (InputPair.leaf A) := by
  obtain ⟨v0, v1, v2, h0, h1, h2, hb, e0, e1, e2⟩ :=
    SpendValues.of_value_balance prime hprime pub A h.1.1 h.2
  refine ⟨v0, v1, v2, h0, h1, h2, hb, e0, e1, e2, ?_⟩
  rw [← e0]
  exact of_production pub A lam chi h

#print axioms of_production
#print axioms bounded_of_production
end AspisR1.InputWitness
