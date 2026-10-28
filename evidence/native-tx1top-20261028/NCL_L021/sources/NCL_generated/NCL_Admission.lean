import Std
set_option autoImplicit false
namespace AspisR1.NCL_Admission

/-- Value predicate checked against frozen pool_route::admitted by the native
route gates. This predicate alone is not an unbounded slice bridge. -/
def admitted (data : List UInt8) : Prop :=
  data=[3,10] ∨ data=[3,11] ∨ ∃ suffix, data=[65,83,81,56]++suffix

/-- TX1's exact two-byte dispatch is a separate case from the ASQ8 route. -/
theorem tx1 (a b : UInt8) : admitted [a,b] ↔ a=3 ∧ (b=10 ∨ b=11) := by
  constructor
  · intro h
    rcases h with h|h|⟨suffix,h⟩
    · have eq := List.cons.inj h
      exact ⟨eq.1,Or.inl (List.cons.inj eq.2).1⟩
    · have eq := List.cons.inj h
      exact ⟨eq.1,Or.inr (List.cons.inj eq.2).1⟩
    · have sizes := congrArg List.length h
      simp only [List.length_cons,List.length_nil,List.length_append] at sizes
      omega
  · rintro ⟨rfl,h|h⟩
    · subst b;exact Or.inl rfl
    · subst b;exact Or.inr (Or.inl rfl)

/-- Admission alone permits split11; the driver's split10 gate must still
be proved on the same instruction. -/
theorem other_split (split : UInt8) (route : admitted [3,split])
    (rejectedGate : split≠10) : split=11 := by
  rcases (tx1 3 split).mp route with ⟨_,h|h⟩
  · exact False.elim (rejectedGate h)
  · exact h

/-- No suffix on a non-ASQ8 prefix becomes a TX1 instruction merely because
it starts with the accepted two bytes. This is an exact list-shape law. -/
theorem tx1_has_no_suffix (suffix : List UInt8) (nonempty : suffix≠[])
    :
    ¬ admitted ([3,10]++suffix) := by
  intro h
  rcases h with h|h|h
  · have sizes := congrArg List.length h
    have length : suffix.length=0 := by simp only [List.length_append,List.length_cons,List.length_nil] at sizes;omega
    exact nonempty (List.length_eq_zero.mp length)
  · have heads := List.cons.inj h
    have tails := List.cons.inj heads.2
    have bad : (10 : UInt8)≠11 := by decide
    exact bad tails.1
  · obtain ⟨rest,h⟩ := h
    have bad : (3 : UInt8)≠65 := by decide
    exact bad (List.cons.inj h).1

#print axioms tx1
#print axioms other_split
#print axioms tx1_has_no_suffix
end AspisR1.NCL_Admission
