import Aeneas
set_option autoImplicit false
namespace R1Z.PV_CB3_EqualityBits

theorem four_xor_zero {w : Nat} (a b c d e f g h : BitVec w) :
    (((a ^^^ b) ||| (c ^^^ d)) ||| (e ^^^ f)) ||| (g ^^^ h) = 0#w ↔
      a=b ∧ c=d ∧ e=f ∧ g=h := by
  simp only [BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff]
  constructor
  · rintro ⟨⟨⟨hab,hcd⟩,hef⟩,hgh⟩; exact ⟨hab,hcd,hef,hgh⟩
  · rintro ⟨hab,hcd,hef,hgh⟩; exact ⟨⟨⟨hab,hcd⟩,hef⟩,hgh⟩

theorem four_xor_nonzero {w : Nat} (a b c d e f g h : BitVec w) :
    (((a ^^^ b) ||| (c ^^^ d)) ||| (e ^^^ f)) ||| (g ^^^ h) ≠ 0#w ↔
      a≠b ∨ c≠d ∨ e≠f ∨ g≠h := by
  rw [ne_eq,four_xor_zero]
  simp only [not_and_or]
#print axioms four_xor_zero
#print axioms four_xor_nonzero
end R1Z.PV_CB3_EqualityBits
