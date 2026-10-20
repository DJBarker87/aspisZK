import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.TerminalV4ActiveLiteralCanonical
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Values := Array QM 16#usize

def valueCell (values : Values) (i : Fin 16) : QM :=
  values.val[i.val]'(by simpa [values.property] using i.isLt)

theorem sum_6144_success_canonical (values : Values) (out : QM)
    (hvalues : ∀ i : Fin 16, CanonicalQM (valueCell values i))
    (hrun : AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16
      values 6144#u16 = .ok out) :
    CanonicalQM out := by
  have h := hrun
  have hcount : core.num.U16.count_ones 6144#u16 = .ok 2#u32 := by
    norm_num [core.num.U16.count_ones, core.num.U16.count_ones_nat,
      core.num.U16.count_ones_aux, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rfl
  rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16,
    hcount] at h
  simp only [bind_tc_ok, show ¬ (2#u32 > 8#u32) by decide, if_false] at h
  change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop
    values 6144#u16 false AspisR1SelectedMaskProbe.field.QM31.ZERO = .ok out at h
  have hloop := h
  rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop.eq_def] at hloop
  simp only [show (6144#u16 != 0#u16) = true by decide, if_true] at hloop
  have htrail11 : core.num.U16.trailing_zeros 6144#u16 = .ok 11#u32 := by
    norm_num [core.num.U16.trailing_zeros, core.num.U16.trailing_zeros_nat,
      core.num.U16.trailing_zeros_aux, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rfl
  have hcast11 : UScalar.cast UScalarTy.Usize 11#u32 = 11#usize := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    have hsrc : (11#u32).val = 11 := by norm_num
    have hdst : (11#usize).val = 11 := by norm_num
    rw [hsrc, hdst]
    apply Nat.mod_eq_of_lt
    rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  have hread11 : Array.index_usize values 11#usize = .ok (valueCell values 11) := by
    have hi : (11#usize).val < values.val.length := by
      simpa [values.property] using (show 11 < 16 by decide)
    obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec values 11#usize hi)
    rw [hread]
    congr 1
  have hz : CanonicalQM AspisR1SelectedMaskProbe.field.QM31.ZERO := by
    unfold CanonicalQM AspisR1.TerminalV4TowerAdd.CanonicalQM
      AspisR1.TerminalV4TowerAdd.CanonicalCM
    simp [AspisR1SelectedMaskProbe.field.QM31.ZERO,
      AspisR1.TerminalV4TowerAdd.P, AspisR1.TerminalV4M31AddSub.P]
  have hq : CanonicalQM (valueCell values 11) := hvalues 11
  obtain ⟨sum1, hadd, hsum1, _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_qm_add_mod
      AspisR1SelectedMaskProbe.field.QM31.ZERO (valueCell values 11) hz hq
  simp only [htrail11, hcast11, lift, bind_tc_ok, hread11,
    if_neg (by decide : ¬ (false = true))] at hloop
  simp only [hadd, bind_tc_ok] at hloop
  have hsub : 6144#u16 - 1#u16 = 6143#u16 := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have hand : 6144#u16 &&& 6143#u16 = 4096#u16 := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.val_and]
    norm_num
  simp only [hsub, hand, bind_tc_ok] at hloop
  trace_state
  exact False.elim (by assumption)
end AspisR1.TerminalV4ActiveLiteralCanonical
