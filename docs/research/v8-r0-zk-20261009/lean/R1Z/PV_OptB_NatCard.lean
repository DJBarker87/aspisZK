import R1Z.PV_OptB_FieldCard
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_NatCard
open R0P

theorem distinct_small_sets {A Public : Type} [Fintype A] [Fintype Public]
    (n k : Nat) (pub : (Fin n → A) → Public)
    (values : (Fin n → A) → Fin n → Finset A)
    (contains : ∀ w i, w i ∈ values w i)
    (bounded : ∀ w i, (values w i).card ≤ k)
    (large : Nat.card Public * k^n < Nat.card A ^ n) :
    ∃ w u, pub w = pub u ∧ values w ≠ values u := by
  apply PV_OptB_Pigeonhole.distinct_small_sets n k pub values contains bounded
  simpa only [Nat.card_eq_fintype_card] using large

theorem large_for {A : Type} [Fintype A] (card : Nat.card A = 2147483647) :
    Nat.card (Digest A) * 4096^16 < Nat.card A ^ 16 := by
  have card' : Fintype.card A = 2147483647 := by
    simpa only [Nat.card_eq_fintype_card] using card
  simpa only [Nat.card_eq_fintype_card] using PV_OptB_FieldCard.large_for card'

#print axioms distinct_small_sets
#print axioms large_for
#check Nat.card_zmod
end R1Z.PV_OptB_NatCard
