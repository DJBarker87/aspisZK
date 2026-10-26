import NP6_StdModel
set_option autoImplicit false
namespace AspisR1.NP6_Initialization

def write {Row : Type} (state : Fin 3 → Option Row) (p : Fin 3) (row : Row) :
    Fin 3 → Option Row := fun j => if j=p then some row else state j

/-- Symbolic loop invariant used with the three real decoder/write gates:
success at all three writes initializes every row, independently of the
uninitialized buffer's prior contents. No large finite reduction is used. -/
theorem complete {Row : Type} (before : Fin 3 → Option Row) (r0 r1 r2 : Row) :
    ∀ j, ∃ row, write (write (write before ⟨0,by decide⟩ r0) ⟨1,by decide⟩ r1)
      ⟨2,by decide⟩ r2 j = some row := by
  intro j
  have alternatives : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
  rcases alternatives with h | h | h
  · have same : j=⟨0,by decide⟩ := Fin.ext h
    subst j
    exact ⟨r0,rfl⟩
  · have same : j=⟨1,by decide⟩ := Fin.ext h
    subst j
    exact ⟨r1,rfl⟩
  · have same : j=⟨2,by decide⟩ := Fin.ext h
    subst j
    exact ⟨r2,rfl⟩

#print axioms complete
end AspisR1.NP6_Initialization
