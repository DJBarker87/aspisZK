import S6BumpOwnedReferenceSourceV1
import S6AlignedAllocationRangeV1
set_option autoImplicit false
namespace AspisS6BumpReferenceExact
open Aeneas Aeneas.Std Result

/-- The COMPLETE emitted owned Rust function is TOTAL for nonzero alignment,
including insufficient-space rejection. Natural arithmetic is its exact result,
not an independent normal-return/success hypothesis. -/
theorem step_total_exact (initial length bytes alignment : Usize)
    (positive : 0 < alignment.val) :
    ∃ out,
      AspisS6BumpOwnedReference.step initial length bytes alignment = ok out ∧
      out.map UScalar.val = AspisS6AlignedAllocationRange.step
        (if initial = 0#usize then length.val else initial.val) bytes.val alignment.val := by
  let cursor : Usize := if initial = 0#usize then length else initial
  have pick : (if initial = 0#usize then ok length else ok initial) = ok cursor := by
    dsimp [cursor]
    split <;> rfl
  have cursorVal : cursor.val = if initial = 0#usize then length.val else initial.val := by
    dsimp [cursor]
    split <;> rfl
  rw [← cursorVal]
  by_cases fits : bytes.val ≤ cursor.val
  · obtain ⟨available,subtract,availableVal⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := cursor) (y := bytes) fits)
    have checked : Usize.checked_sub cursor bytes = some available := by
      simp only [Usize.checked_sub,core.num.checked_sub_UScalar,subtract,Option.ofResult]
    obtain ⟨quotient,divide,quotientVal⟩ := WP.spec_imp_exists
      (Usize.div_spec available (y := alignment) (by omega))
    have productBound : quotient.val*alignment.val ≤ Usize.max := by
      rw [quotientVal]
      have bounded := Nat.div_mul_le_self available.val alignment.val
      have maxBound : available.val ≤ Usize.max := by scalar_tac
      omega
    obtain ⟨next,multiply,nextVal⟩ := WP.spec_imp_exists
      (Usize.mul_spec (x := quotient) (y := alignment) productBound)
    have value : next.val = ((cursor.val-bytes.val)/alignment.val)*alignment.val := by
      rw [nextVal,quotientVal,availableVal.1]
    refine ⟨if next < 8#usize then none else some next,?_,?_⟩
    · unfold AspisS6BumpOwnedReference.step
      rw [pick]
      simp only [bind_tc_ok,checked,lift,
        AspisS6BumpOwnedReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        divide,multiply]
    · rw [AspisS6AlignedAllocationRange.step,if_pos fits,← value]
      by_cases header : 8 ≤ next.val
      · have comparison : ¬ next < 8#usize := by
          simp only [UScalar.lt_equiv]
          change ¬ next.val < 8
          omega
        simp only [comparison,if_false,Option.map_some,header,if_true]
      · have comparison : next < 8#usize := by
          simp only [UScalar.lt_equiv]
          change next.val < 8
          omega
        simp only [comparison,if_true,Option.map_none,header,if_false]
  · have underflow : cursor.val < bytes.val := by omega
    have checked : Usize.checked_sub cursor bytes = none := by
      simp [Usize.checked_sub,core.num.checked_sub_UScalar,UScalar.sub,underflow,Option.ofResult]
    refine ⟨none,?_,?_⟩
    · unfold AspisS6BumpOwnedReference.step
      rw [pick]
      simp only [bind_tc_ok,checked,lift,
        AspisS6BumpOwnedReference.core.option.Option.Insts.CoreOpsTry_traitTry.branch]
      rfl
    · simp only [Option.map_none,AspisS6AlignedAllocationRange.step,fits,if_false]

#print axioms step_total_exact
end AspisS6BumpReferenceExact
