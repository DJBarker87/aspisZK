import NEO_ParserReference
set_option autoImplicit false
namespace NEO_ParserTotal
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

theorem eight (xs : Array U32 8#usize) :
    ∃ a b c d e f g h : U32, xs = Array.make 8#usize [a,b,c,d,e,f,g,h] := by
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

/-- Complete raw fixed-array Result association, not just constructor-shaped inputs. -/
theorem result (xs : Array U32 8#usize) :
    NEO_ParserRef.limbs_ref xs =
      (do
        let parsed ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs xs
        match parsed with
        | none => ok none
        | some value => do
          let words ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
          ok (some words)) := by
  obtain ⟨a,b,c,d,e,f,g,h,rfl⟩ := eight xs
  exact NEO_ParserReference.limbs a b c d e f g h

/-- Both rejected and accepted outputs retain the complete native carrier. -/
theorem option_lossless (x y : Option E)
    (same : x.map NEB_ArrayRefs.wordsE = y.map NEB_ArrayRefs.wordsE) : x=y := by
  cases x with
  | none => cases y <;> simp_all
  | some x =>
    cases y with
    | none => simp_all
    | some y =>
      have words : NEB_ArrayRefs.wordsE x=NEB_ArrayRefs.wordsE y := Option.some.inj same
      exact congrArg some (NEB_ArrayRefs.wide_injective words)

#print axioms eight
#print axioms result
#print axioms option_lossless
end NEO_ParserTotal
