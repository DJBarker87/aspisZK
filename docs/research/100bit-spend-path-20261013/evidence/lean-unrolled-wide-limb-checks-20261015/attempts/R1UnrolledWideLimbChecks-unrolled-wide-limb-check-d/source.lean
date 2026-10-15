import UnrolledWideParserSource

/-! Fixed-size normalization for the retained unrolled eight-limb parser. -/
set_option autoImplicit false

namespace AspisR1.UnrolledWideLimbChecks

open Aeneas Aeneas.Std Result

theorem from_limbs_make (a0 a1 a2 a3 a4 a5 a6 a7 : U32) :
    AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled
      (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) =
    Result.ok
      (if a0 ≥ AspisR1CandidateParser.field.P ∨
          a1 ≥ AspisR1CandidateParser.field.P ∨
          a2 ≥ AspisR1CandidateParser.field.P ∨
          a3 ≥ AspisR1CandidateParser.field.P ∨
          a4 ≥ AspisR1CandidateParser.field.P ∨
          a5 ≥ AspisR1CandidateParser.field.P ∨
          a6 ≥ AspisR1CandidateParser.field.P ∨
          a7 ≥ AspisR1CandidateParser.field.P then none else
        some { c0 := { c0 := { a := a0, b := a1 }, c1 := { a := a2, b := a3 } },
               c1 := { c0 := { a := a4, b := a5 }, c1 := { a := a6, b := a7 } } }) := by
  by_cases h0 : AspisR1CandidateParser.field.P ≤ a0
  · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
      Array.index_usize, Array.make, h0]
  · by_cases h1 : AspisR1CandidateParser.field.P ≤ a1
    · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
        Array.index_usize, Array.make, h0, h1]
    · by_cases h2 : AspisR1CandidateParser.field.P ≤ a2
      · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
          Array.index_usize, Array.make, h0, h1, h2]
      · by_cases h3 : AspisR1CandidateParser.field.P ≤ a3
        · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
            Array.index_usize, Array.make, h0, h1, h2, h3]
        · by_cases h4 : AspisR1CandidateParser.field.P ≤ a4
          · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
              Array.index_usize, Array.make, h0, h1, h2, h3, h4]
          · by_cases h5 : AspisR1CandidateParser.field.P ≤ a5
            · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
                Array.index_usize, Array.make, h0, h1, h2, h3, h4, h5]
            · by_cases h6 : AspisR1CandidateParser.field.P ≤ a6
              · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
                  Array.index_usize, Array.make, h0, h1, h2, h3, h4, h5, h6]
              · by_cases h7 : AspisR1CandidateParser.field.P ≤ a7
                · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
                    Array.index_usize, Array.make, h0, h1, h2, h3, h4, h5, h6, h7]
                · simp [AspisR1CandidateParser.field.wide_exact.WideExact.from_limbs_unrolled,
                    Array.index_usize, Array.make, h0, h1, h2, h3, h4, h5, h6, h7]

#print axioms from_limbs_make

end AspisR1.UnrolledWideLimbChecks
