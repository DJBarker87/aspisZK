import AspisR1.CopyPatternLoopFactor

/-! Actual sixteen-lane pattern loop against the retained symbolic suffix fold. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternLoopFuel
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact AspisR1.CopyPatternLoopFactor
open AspisR1.CopyPatternFoldModel

theorem pattern_loop_success_fuel (openings powers : Array QM 16#usize)
    (limb : Usize) (pattern : Pattern) (value : QM) (fuel : Nat)
    (hspan : limb.val + fuel = 16)
    (hcolumns : ∀ j : Fin 16, (cell pattern.columns j).val < 16)
    (hoffsets : ∀ j : Fin 16, (cell pattern.offsets j).val < AspisR1.TerminalLiftM31Exact.P)
    (hopenings : AspisR1.ArrayUpdateCanonicalExact.CanonicalArray openings)
    (hpowers : AspisR1.ArrayUpdateCanonicalExact.CanonicalArray powers)
    (hvalue : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM value) :
    ∃ out, Loop openings powers limb pattern value = .ok (16#usize,out) ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      decode out = remaining (modelPattern pattern hcolumns)
        (decodedCells openings) (decodedCells powers) limb.val (decode value) := by
  have hwidth : Width.val = 16 := by
    unfold Width AspisR1CopyPatternCandidate.poseidon2.POSEIDON2_WIDTH
    scalar_tac
  induction fuel generalizing limb value with
  | zero =>
    have hlimb : limb.val = 16 := by omega
    have hstop : ¬ limb < Width := by change ¬ limb.val < Width.val; omega
    have hlimbEq : limb = 16#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hlimb
    refine ⟨value,?_,hvalue,?_⟩
    · unfold Loop
      rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0.eq_def,
        if_neg hstop,hlimbEq]
    · rw [hlimb,remaining_end]
  | succ fuel ih =>
    have hlimb : limb.val < 16 := by omega
    have hlt : limb < Width := by change limb.val < Width.val; omega
    obtain ⟨value1,hrun,hcvalue1,hvvalue1⟩ :=
      limb_success openings powers limb pattern value hlimb hcolumns hoffsets hopenings hpowers hvalue
    obtain ⟨limb1,hnext,hnextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := limb) (y := 1#usize) (by scalar_tac))
    have hnextVal : limb1.val = limb.val + 1 := by simpa using hnextValue
    have hspan1 : limb1.val + fuel = 16 := by omega
    obtain ⟨out,hrec,hcout,hvout⟩ := ih limb1 value1 hspan1 hcvalue1
    refine ⟨out,?_,hcout,?_⟩
    · rw [loop_step_eq openings powers limb pattern value hlt]
      simp only [hrun,hnext,bind_tc_ok]
      exact hrec
    · rw [remaining_step (modelPattern pattern hcolumns)
        (decodedCells openings) (decodedCells powers) ⟨limb.val,hlimb⟩ (decode value)]
      simpa only [hnextVal,hvvalue1] using hvout

#print axioms pattern_loop_success_fuel
end
end AspisR1.CopyPatternLoopFuel
