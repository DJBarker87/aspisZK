import AspisR1.CopyPatternPowerSource
import AspisR1.CopyPatternPowerModel
import ArrayUpdateCanonicalExact
import ExtractedMaskQM31Exact

/-! Exact symbolic traversal of the source16-power initialization loop. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternPowerLoop
noncomputable section
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact AspisR1.CopyPatternPowerModel
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev QM := field.QM31
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Loop := AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0
abbrev Width := AspisR1CopyPatternCandidate.poseidon2.POSEIDON2_WIDTH

theorem powers_loop_success_fuel (lambda : QM) (powers : Array QM 16#usize)
    (power : QM) (limb : Usize) (fuel : Nat)
    (hspan : limb.val + fuel = 16)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda)
    (hpowers : CanonicalArray powers)
    (hpower : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM power)
    (hvalue : decode power = powerAt (decode lambda) limb.val)
    (hprefix : ∀ j : Fin (16#usize).val, j.val < limb.val →
      decode (cells powers j) = powerAt (decode lambda) j.val) :
    ∃ out, Loop lambda powers power limb = .ok (out,16#usize) ∧
      CanonicalArray out ∧
      ∀ j : Fin (16#usize).val,
        decode (cells out j) = powerAt (decode lambda) j.val := by
  have hwidth : Width.val = 16 := by
    unfold Width AspisR1CopyPatternCandidate.poseidon2.POSEIDON2_WIDTH
    scalar_tac
  induction fuel generalizing powers power limb with
  | zero =>
    have hlimb : limb.val = 16 := by omega
    have hstop : ¬ limb < Width := by
      change ¬ limb.val < Width.val
      omega
    have hlimbEq : limb = 16#usize := by
      apply UScalar.eq_of_val_eq
      simpa using hlimb
    refine ⟨powers,?_,hpowers,?_⟩
    · unfold Loop
      rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0.eq_def,
        if_neg hstop, hlimbEq]
    · intro j
      exact hprefix j (by have hj := j.isLt; simp only [UScalar.ofNatCore_val_eq] at hj; omega)
  | succ fuel ih =>
    have hlimb : limb.val < 16 := by omega
    have hbound : limb.val < (16#usize).val := by simpa using hlimb
    have hlt : limb < Width := by
      change limb.val < Width.val
      omega
    obtain ⟨updated,hupdate,hcupdated,hframe⟩ :=
      update_success powers limb power hbound hpowers hpower
    obtain ⟨power1,hmul,hcpower1,hvpower1⟩ :=
      AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact power lambda hpower hlambda
    change decode power1 = decode power * decode lambda at hvpower1
    obtain ⟨limb1,hnext,hnextValue⟩ := WP.spec_imp_exists
      (Usize.add_spec (x := limb) (y := 1#usize) (by scalar_tac))
    have hnextVal : limb1.val = limb.val + 1 := by simpa using hnextValue
    have hspan1 : limb1.val + fuel = 16 := by omega
    have hvpower : decode power1 = powerAt (decode lambda) limb1.val := by
      rw [hvpower1,hvalue,hnextVal,powerAt_succ]
    let pos : Fin (16#usize).val := ⟨limb.val,hbound⟩
    have hprefix1 : ∀ j : Fin (16#usize).val, j.val < limb1.val →
        decode (cells updated j) = powerAt (decode lambda) j.val := by
      intro j hj
      change decode (cells updated j) = _
      rw [hframe]
      by_cases he : j = (⟨limb.val,hbound⟩ : Fin (16#usize).val)
      · subst j
        simpa [Function.update] using hvalue
      · have hne : j.val ≠ limb.val := by
          intro hv
          apply he
          apply Fin.ext
          exact hv
        have hjOld : j.val < limb.val := by omega
        simpa [Function.update, he] using hprefix j hjOld
    obtain ⟨out,hrec,hcout,hout⟩ :=
      ih updated power1 limb1 hspan1 hcupdated hcpower1 hvpower hprefix1
    refine ⟨out,?_,hcout,hout⟩
    unfold Loop
    rw [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0.eq_def]
    simp only [hlt, if_pos, hupdate, hmul, hnext, bind_tc_ok]
    exact hrec

#print axioms powers_loop_success_fuel
end
end AspisR1.CopyPatternPowerLoop
