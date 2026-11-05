import NHT_COMBINED_IMPORT
import NHV_NEO_WindowPrefix

set_option autoImplicit false
namespace NEO_ComplexTotal
open Aeneas Aeneas.Std Result
theorem eight (xs : Array U8 8#usize) :
    ∃ a b c d e f g h : U8, xs = Array.make 8#usize [a,b,c,d,e,f,g,h] := by
  rcases xs with ⟨xs,size⟩
  change xs.length=8 at size
  cases xs with
  | nil => simp at size
  | cons a xs =>
    cases xs with
    | nil => simp at size
    | cons b xs =>
      cases xs with
      | nil => simp at size
      | cons c xs =>
        cases xs with
        | nil => simp at size
        | cons d xs =>
          cases xs with
          | nil => simp at size
          | cons e xs =>
            cases xs with
            | nil => simp at size
            | cons f xs =>
              cases xs with
              | nil => simp at size
              | cons g xs =>
                cases xs with
                | nil => simp at size
                | cons h xs =>
                  have empty : xs=[] := by
                    apply List.eq_nil_of_length_eq_zero
                    simp only [List.length_cons] at size
                    omega
                  subst xs
                  exact ⟨a,b,c,d,e,f,g,h,rfl⟩


theorem fixed (xs : Array U8 8#usize) :
 NEO_WindowV2.complex xs.to_slice = NEO_ComplexReference.cohort xs.to_slice := by
 obtain ⟨a,b,c,d,e,f,g,h,rfl⟩ := eight xs
 exact NEO_ComplexReference.eight a b c d e f g h

theorem result (bytes : Slice U8) (bound : 8≤bytes.val.length) :
 NEO_WindowV2.complex bytes = NEO_ComplexReference.cohort bytes := by
 rw [NEO_WindowPrefix.complex bytes bound]
 apply (fixed _).trans
 unfold NEO_ComplexReference.cohort
 rw [NEO_PrefixSlices.complex bytes bound]

theorem observe_injective (x y : AspisR1CandidateParser.field.CM31)
 (h : NEO_ComplexReference.observe x=NEO_ComplexReference.observe y) : x=y := by
 cases x; cases y
 simp [NEO_ComplexReference.observe,Array.make] at h
 rcases h with ⟨rfl,rfl⟩
 rfl

#print axioms eight
#print axioms fixed
#print axioms result
#print axioms observe_injective
end NEO_ComplexTotal
