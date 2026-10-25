import ExtractedMaskCoefficientStep
import ExtractedMaskForwardRange

/-! Symbolic execution contract for the complete generated coefficient loop 0.
    `writeModel0` is a fuel-indexed sequence of direct coefficient writes; the
    proof uses the generic iterator/body contracts and never unfolds the 16
    loop iterations. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskCoefficientLoop0

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientStep
open AspisR1.ExtractedMaskForwardRange

abbrev QM := field.QM31
abbrev C1 := AspisR1.ExtractedMaskCoefficientStep.C1
abbrev Coefficients := AspisR1.ExtractedMaskCoefficientStep.Coefficients
abbrev Range := core.ops.range.Range Usize
abbrev CanonicalQM := AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
abbrev CanonicalArray := AspisR1.ExtractedMaskCoefficientStep.CanonicalArray

/-- One mathematical coefficient write, retaining the actual extracted basis
    multiplication and source table lookup as symbolic operations. -/
def writeAt0 (c1 : C1) (coefficients : Coefficients)
    (column : Usize) (hcolumn : column.val < 16) : Coefficients :=
  let q := c1.val[column.val]'(by simpa [c1.property] using hcolumn)
  let basis := column &&& 3#usize
  let transformed :=
    match state_only_hiding.mul_tower_basis q basis with
    | .ok z => z
    | .fail _ => field.QM31.ZERO
    | .div => field.QM31.ZERO
  let exponent := core.convert.num.FromUsizeU8.from
    (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
      (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn))
  coefficients.set exponent transformed

/-- Fuel-indexed symbolic writes over the exact forward iterator. This is a
    finite fold of coefficient updates, not an unfolding of the generated loop. -/
def writeModel0 (c1 : C1) (coefficients : Coefficients) (iter : Range) :
    Nat → Coefficients
  | 0 => coefficients
  | fuel + 1 =>
      match core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
      | .ok (none, _) => coefficients
      | .ok (some column, iter1) =>
          if hcolumn : column.val < 16 then
            writeModel0 c1 (writeAt0 c1 coefficients column hcolumn) iter1 fuel
          else coefficients
      | .fail _ => coefficients
      | .div => coefficients

/-- Whole-loop correctness for any subrange ending at 16. `sourceCanonical`
    and `initialCanonical` are the only data invariants required by the
    pointwise body contract. -/
theorem loop0_exec (c1 : C1) (iter : Range) (coefficients : Coefficients)
    (fuel : Nat)
    (hend : iter.end.val = 16)
    (hspan : iter.start.val + fuel = 16)
    (hsource : ∀ j : Fin 16, CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hinitial : CanonicalArray coefficients) :
    ∃ out : Coefficients,
      state_only_hiding.state_only_selected_mask_value_loop0 iter c1 coefficients = .ok out ∧
      CanonicalArray out ∧
      out = writeModel0 c1 coefficients iter fuel := by
  induction fuel generalizing iter coefficients with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hnext := next_done iter hstop
      have hbody := loop0_body_done c1 iter coefficients iter hnext
      refine ⟨coefficients, ?_, hinitial, rfl⟩
      rw [state_only_hiding.state_only_selected_mask_value_loop0, loop.eq_def]
      dsimp only
      simp only [hbody, bind_tc_ok]
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _hchecked⟩ := next_step iter hlt
      have hcolumn : iter.start.val < 16 := by omega
      obtain ⟨transformed, updated, hbody, htransformedCanonical,
        htransformedValue, hset, hupdatedCanonical⟩ :=
        loop0_body_step c1 iter iter1 coefficients iter.start hnext hcolumn
          hsource hinitial
      have hspan1 : iter1.start.val + fuel = 16 := by omega
      have hend1' : iter1.end.val = 16 := by rw [hend1, hend]
      have hrec := ih iter1 updated hend1' hspan1 hupdatedCanonical
      obtain ⟨out, hrun, houtCanonical, hmodel⟩ := hrec

      let q := c1.val[iter.start.val]'(by
        simpa [c1.property] using hcolumn)
      let basis := iter.start &&& 3#usize
      have hq : CanonicalQM q := by
        have hj : (⟨iter.start.val, hcolumn⟩ : Fin 16).val = iter.start.val := rfl
        simpa [q, AspisR1.ExtractedMaskCoefficientStep.c1Cell, hj] using
          hsource ⟨iter.start.val, hcolumn⟩
      have hcoord : basis.val < 4 := by
        rw [AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four
          iter.start (by omega)]
        exact Nat.mod_lt _ (by omega)
      obtain ⟨transformed', htransform, _hcanon', _hvalue'⟩ :=
        AspisR1.ExtractedMaskTowerBasisExact.current_mul_tower_basis_exact
          q basis hq hcoord
      obtain ⟨tableValue, htable, htableValue⟩ :=
        AspisR1.ExtractedMaskCoefficientSchedule.factor_table_lookup
          iter.start (by omega)
      let destination := core.convert.num.FromUsizeU8.from tableValue
      have hdestinationValue : destination.val =
          (AspisR1.ExtractedMaskCoefficientArray.c1Exponent
            ⟨iter.start.val, hcolumn⟩).val := by
        simpa [destination, core.convert.num.FromUsizeU8.from_val_eq] using
          htableValue
      have hdestination : destination.val < 27 := by
        rw [hdestinationValue]
        exact (AspisR1.ExtractedMaskCoefficientArray.c1Exponent
          ⟨iter.start.val, hcolumn⟩).isLt
      have hupdateBound : destination.val < coefficients.length := by
        simpa [coefficients.property] using hdestination
      obtain ⟨updated', hupdate, hset'⟩ :=
        WP.spec_imp_exists (Array.update_spec coefficients destination transformed' hupdateBound)
      have htableRaw : Array.index_usize state_only_hiding.FACTOR_EXPONENTS
          iter.start = .ok (state_only_hiding.FACTOR_EXPONENTS.val[iter.start.val]'
            (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)) := by
        exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
          state_only_hiding.FACTOR_EXPONENTS iter.start
            (by simpa using hcolumn)
      have htableEq : tableValue =
          state_only_hiding.FACTOR_EXPONENTS.val[iter.start.val]'
            (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn) :=
        Result.ok.inj (htable.symm.trans htableRaw)
      have hbody' : state_only_hiding.state_only_selected_mask_value_loop0.body
          c1 iter coefficients = .ok (.cont (iter1, updated')) := by
        have hget : Array.index_usize c1 iter.start = .ok q := by
          exact AspisR1.ExtractedMaskHornerStep.array_index_usize_ok c1 iter.start
            (by simpa [c1.property] using hcolumn)
        simp only [state_only_hiding.state_only_selected_mask_value_loop0.body,
          hnext, bind_tc_ok, hget, lift, q, basis, htransform, htable,
          destination, hupdate]
      have hpair := ControlFlow.cont.inj
        (Result.ok.inj (hbody.symm.trans hbody'))
      have hupdated' : updated = updated' := congrArg Prod.snd hpair
      have hcell : core.convert.num.FromUsizeU8.from
          (state_only_hiding.FACTOR_EXPONENTS.val[iter.start.val]'
            (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)) =
          destination := by
        apply UScalar.eq_of_val_eq
        simp [destination, core.convert.num.FromUsizeU8.from_val_eq, htableEq]
      have hsetAt : updated = coefficients.set destination transformed := by
        rw [hcell] at hset
        exact hset
      have htransformed' : transformed = transformed' := by
        have hget := congrArg
          (fun a : Coefficients => a[destination]'(by
            simpa [a.property] using hdestination)) hupdated'
        rw [hsetAt, hset'] at hget
        have hboundTransformed : destination.val <
            (coefficients.set destination transformed).length := by simpa using hupdateBound
        have hboundTransformed' : destination.val <
            (coefficients.set destination transformed').length := by simpa using hupdateBound
        rw [Array.getElem_set_eq coefficients destination transformed hboundTransformed,
          Array.getElem_set_eq coefficients destination transformed' hboundTransformed'] at hget
        exact hget
      have hwrite : writeAt0 c1 coefficients iter.start hcolumn = updated := by
        unfold writeAt0
        simp only [q, basis, htransform]
        rw [hcell, ← htransformed']
        exact hsetAt.symm

      refine ⟨out, ?_, houtCanonical, ?_⟩
      · rw [state_only_hiding.state_only_selected_mask_value_loop0, loop.eq_def]
        dsimp only
        simp only [hbody, bind_tc_ok]
        exact hrun
      · rw [writeModel0, hnext]
        simp only [hcolumn, ↓reduceDIte, hwrite]
        exact hmodel

#print axioms writeAt0
#print axioms writeModel0
#print axioms loop0_exec

end AspisR1.ExtractedMaskCoefficientLoop0
