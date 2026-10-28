import Aeneas
set_option autoImplicit false
namespace AspisR1.NCN_MismatchWitness

/-- A symbolic mismatching byte is a complete cover of arbitrary unequal
same-length digest replies, rather than a chosen one-bit corruption class. -/
theorem mismatch_witness {α : Type} (xs ys : List α)
    (size : xs.length=ys.length) (different : xs≠ys) :
    ∃ i, ∃ hi : i<xs.length, ∃ hj : i<ys.length, xs[i]≠ys[i] := by
  classical
  by_contra noWitness
  apply different
  apply List.ext_getElem
  · exact size
  · intro i hi hj
    by_contra bad
    exact noWitness ⟨i,hi,hj,bad⟩

#print axioms mismatch_witness
end AspisR1.NCN_MismatchWitness
