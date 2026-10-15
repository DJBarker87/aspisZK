import AspisR1RecordParser.Funs

/-!
Canonical limb bounds and exact packing for the actual attempt-F constructor.
This does not prove byte-decoder, base-field, validator-loop, or Rust refinement.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedRecordLimbCanonicality
open Aeneas Aeneas.Std Result
open AspisR1RecordParser.field.wide_exact

/-- Packing used by the actual eight-limb constructor, with no reduction. -/
def packed (a0 a1 a2 a3 a4 a5 a6 a7 : U32) : WideExact :=
  { c0 := { c0 := { a := a0, b := a1 }, c1 := { a := a2, b := a3 } },
    c1 := { c0 := { a := a4, b := a5 }, c1 := { a := a6, b := a7 } } }

/-- Exact normal form of the generated constructor's eight ordered guards. -/
theorem from_limbs_make (a0 a1 a2 a3 a4 a5 a6 a7 : U32) :
    WideExact.from_limbs (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) =
      ok (if 2147483647 ≤ a0.val ∨ 2147483647 ≤ a1.val ∨
          2147483647 ≤ a2.val ∨ 2147483647 ≤ a3.val ∨
          2147483647 ≤ a4.val ∨ 2147483647 ≤ a5.val ∨
          2147483647 ≤ a6.val ∨ 2147483647 ≤ a7.val then none
        else some (packed a0 a1 a2 a3 a4 a5 a6 a7)) := by
  simp only [WideExact.from_limbs, Array.index_usize, Array.make]
  by_cases h0 : 2147483647 ≤ a0.val
  · simp [h0, AspisR1RecordParser.field.P]
  · by_cases h1 : 2147483647 ≤ a1.val
    · simp [h0, h1, AspisR1RecordParser.field.P]
    · by_cases h2 : 2147483647 ≤ a2.val
      · simp [h0, h1, h2, AspisR1RecordParser.field.P]
      · by_cases h3 : 2147483647 ≤ a3.val
        · simp [h0, h1, h2, h3, AspisR1RecordParser.field.P]
        · by_cases h4 : 2147483647 ≤ a4.val
          · simp [h0, h1, h2, h3, h4, AspisR1RecordParser.field.P]
          · by_cases h5 : 2147483647 ≤ a5.val
            · simp [h0, h1, h2, h3, h4, h5, AspisR1RecordParser.field.P]
            · by_cases h6 : 2147483647 ≤ a6.val
              · simp [h0, h1, h2, h3, h4, h5, h6, AspisR1RecordParser.field.P]
              · by_cases h7 : 2147483647 ≤ a7.val
                · simp [h0, h1, h2, h3, h4, h5, h6, h7,
                    AspisR1RecordParser.field.P]
                · simp [h0, h1, h2, h3, h4, h5, h6, h7,
                    AspisR1RecordParser.field.P, packed]

/-- Success is exactly canonical input limbs and their unchanged packing. -/
theorem from_limbs_make_success_iff
    (a0 a1 a2 a3 a4 a5 a6 a7 : U32) (w : WideExact) :
    WideExact.from_limbs (Array.make 8#usize [a0, a1, a2, a3, a4, a5, a6, a7]) =
        ok (some w) ↔
      (∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7], a.val < 2147483647) ∧
      w = packed a0 a1 a2 a3 a4 a5 a6 a7 := by
  rw [from_limbs_make]
  split_ifs with h
  · simp only [Result.ok.injEq, reduceCtorEq, false_iff]
    rintro ⟨hc, _⟩
    have hnot : ¬ (2147483647 ≤ a0.val ∨ 2147483647 ≤ a1.val ∨
        2147483647 ≤ a2.val ∨ 2147483647 ≤ a3.val ∨
        2147483647 ≤ a4.val ∨ 2147483647 ≤ a5.val ∨
        2147483647 ≤ a6.val ∨ 2147483647 ≤ a7.val) := by
      simpa [not_or, not_le] using hc
    exact hnot h
  · simp only [Result.ok.injEq, Option.some.injEq]
    have hc : ∀ a ∈ [a0, a1, a2, a3, a4, a5, a6, a7], a.val < 2147483647 := by
      simpa [not_or, not_le] using h
    exact ⟨fun hw => ⟨hc, hw.symm⟩, fun hw => hw.2.symm⟩

end AspisR1.ExtractedRecordLimbCanonicality

#print axioms AspisR1.ExtractedRecordLimbCanonicality.from_limbs_make
#print axioms AspisR1.ExtractedRecordLimbCanonicality.from_limbs_make_success_iff
