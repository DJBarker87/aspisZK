import AspisR1.CopyPatternSingleExact
import AspisR1.CopyPatternOuterSource

/-! Actual outer fourteen-pattern traversal, retaining canonical arrays and prefix values. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternOuterExact
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact (CanonicalArray cells update_success)
open AspisR1.CopyPatternLimbExact AspisR1.CopyPatternRegistryModel
abbrev OuterLoop := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1
abbrev Count := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1

theorem patterns_outer_success_fuel (openings powers : Array QM 16#usize)
    (lambda : ExactQM) (limb : Usize) (result : Array QM 14#usize)
    (index : Usize) (fuel : Nat) (hspan : index.val + fuel = 14)
    (hopenings : CanonicalArray openings) (hpowers : CanonicalArray powers)
    (hpowersModel : decodedCells powers = R0P.copyPowers lambda)
    (hresult : CanonicalArray result)
    (hprefix : ∀ j : Fin (14#usize).val, j.val < index.val →
      decode (cells result j) = R0P.copyPatternValuesLiteral (decodedCells openings) lambda j) :
    ∃ out, OuterLoop openings powers limb result index = .ok out ∧
      CanonicalArray out ∧
      ∀ j : Fin (14#usize).val, decode (cells out j) =
        R0P.copyPatternValuesLiteral (decodedCells openings) lambda j := by
  have hcount : Count.val = 14 := by
    unfold Count AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
    scalar_tac
  induction fuel generalizing limb result index with
  | zero =>
    have hindex : index.val = 14 := by omega
    have hstop : ¬ index < Count := by change ¬ index.val < Count.val; omega
    refine ⟨result,?_,hresult,?_⟩
    · unfold OuterLoop
      rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1.eq_def,
        if_neg hstop]
    · intro j
      exact hprefix j (by have hj := j.isLt; simp only [UScalar.ofNatCore_val_eq] at hj; omega)
  | succ fuel ih =>
    have hindex : index.val < 14 := by omega
    have hbound : index.val < (14#usize).val := by simpa using hindex
    have hlt : index < Count := by change index.val < Count.val; omega
    have hread := registry_read index hindex
    obtain ⟨value,hinner,hcvalue,hvvalue⟩ :=
      AspisR1.CopyPatternSingleExact.pattern_source_exact openings powers lambda
        ⟨index.val,hindex⟩ hopenings hpowers hpowersModel
    obtain ⟨updated,hupdate,hcupdated,hframe⟩ :=
      update_success result index value hbound hresult hcvalue
    obtain ⟨index1,hnext,hnextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    have hnextVal : index1.val = index.val + 1 := by simpa using hnextValue
    have hspan1 : index1.val + fuel = 14 := by omega
    have hprefix1 : ∀ j : Fin (14#usize).val, j.val < index1.val →
        decode (cells updated j) = R0P.copyPatternValuesLiteral (decodedCells openings) lambda j := by
      intro j hj
      rw [hframe]
      by_cases he : j = (⟨index.val,hbound⟩ : Fin (14#usize).val)
      · subst j
        have hfin : (⟨index.val,hindex⟩ : Fin 14) =
            (⟨index.val,hbound⟩ : Fin (14#usize).val) := by
          apply Fin.ext
          rfl
        have hvvalue1 := hvvalue
        rw [hfin] at hvvalue1
        simpa [Function.update] using hvvalue1
      · have hne : j.val ≠ index.val := by
          intro hv
          apply he
          exact Fin.ext hv
        have hjOld : j.val < index.val := by omega
        simpa [Function.update,he] using hprefix j hjOld
    obtain ⟨out,hrec,hcout,hout⟩ :=
      ih (limb := 16#usize) (result := updated) (index := index1)
        hspan1 hcupdated hprefix1
    refine ⟨out,?_,hcout,hout⟩
    unfold OuterLoop
    rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1.eq_def]
    simp only [hlt,if_pos,hread,hinner,hupdate,hnext,bind_tc_ok]
    exact hrec

#print axioms patterns_outer_success_fuel
end
end AspisR1.CopyPatternOuterExact
