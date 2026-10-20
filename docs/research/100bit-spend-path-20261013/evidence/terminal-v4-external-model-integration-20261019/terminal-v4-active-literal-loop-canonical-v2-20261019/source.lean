import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
import AspisR1.TerminalV4ActiveLiteralCanonical
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.TerminalV4ActiveLiteralLoopCanonical
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Selectors := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors
abbrev Active := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop
abbrev Masks := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS
abbrev SumMask := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16

def highCell (s : Selectors) (i : Fin 64) : QM :=
  s.high.val[i.val]'(by simpa [s.high.property] using i.isLt)

def maskStepOK (s : Selectors) : Prop :=
  ∀ (b : Usize), b.val < 64 →
    ∃ mask, Array.index_usize Masks b = .ok mask ∧
      (mask = 0#u16 ∨ ∃ q, SumMask s.low mask = .ok q ∧ Canonical q)

private theorem usize_add_one_success (b : Usize) (hb : b.val < 64) :
    ∃ b1 : Usize, UScalar.add b 1#usize = .ok b1 ∧ b1.val = b.val + 1 := by
  have hmax := Usize.cMax_bound_concrete.1
  have hsum : b.val + 1 ≤ Usize.max := by omega
  have hchecked : (b + 1#usize : Result Usize) ⦃ z => z.val = b.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨b1, heq, hv⟩ := WP.spec_imp_exists hchecked
  refine ⟨b1, ?_, hv⟩
  change (b + 1#usize : Result Usize) = .ok b1
  exact heq

theorem active_loop_good (n : Nat) (s : Selectors) (block : Usize) (sum out : QM)
    (hbound : block.val + n = 64)
    (hsum : Canonical sum)
    (hhigh : ∀ i : Fin 64, Canonical (highCell s i))
    (hmask : maskStepOK s)
    (hrun : Active s sum block = .ok out) : Canonical out := by
  induction n generalizing block sum out with
  | zero =>
      have hblock : block.val = 64 := by omega
      have hnot : ¬ block < 64#usize := by scalar_tac
      have h := hrun
      rw [Active.eq_def] at h
      simp only [if_neg hnot] at h
      have hout : out = sum := Result.ok.inj h.symm
      simpa [hout] using hsum
  | succ n ih =>
      have hb : block.val < 64 := by omega
      have hlt : block < 64#usize := by scalar_tac
      obtain ⟨mask, hmaskRead, hsumMask⟩ := hmask block hb
      have h := hrun
      rw [Active.eq_def] at h
      simp only [if_pos hlt, hmaskRead, bind_tc_ok] at h
      obtain ⟨block1, hinc, hincVal⟩ := usize_add_one_success block hb
      rcases hsumMask with hzero | ⟨selected, hselected, hselectedCan⟩
      · have hmaskFalse : (mask != 0#u16) = false := by rw [hzero]; decide
        simp only [hmaskFalse, if_false, hinc, bind_tc_ok] at h
        have hnext : block1.val + n = 64 := by rw [hincVal]; omega
        exact ih block1 sum out hnext hsum hhigh hmask h
      · have hmaskTrue : (mask != 0#u16) = true := by
          have hne : mask ≠ 0#u16 := by intro heq; subst mask; simp at hselected
          simp [hne]
        have hhiRead : Array.index_usize s.high block = .ok (highCell s ⟨block.val, hb⟩) := by
          have hi : block.val < s.high.val.length := by simpa [s.high.property] using hb
          obtain ⟨q, hread, hval⟩ := WP.spec_imp_exists (Array.index_usize_spec s.high block hi)
          rw [hread]
          congr 1
        have hhi : Canonical (highCell s ⟨block.val, hb⟩) := hhigh ⟨block.val, hb⟩
        obtain ⟨prod, hmul, hprod⟩ :=
          AspisR1.TerminalV4QM31MulCurrent.current_qm_mul_words
            (highCell s ⟨block.val, hb⟩) selected hhi hselectedCan
        obtain ⟨sum1, hadd, hsum1, _⟩ :=
          AspisR1.TerminalV4TowerAdd.current_qm_add_mod sum prod hsum hprod
        simp only [hmaskTrue, if_true, hhiRead, bind_tc_ok, hselected, bind_tc_ok,
          hmul, bind_tc_ok, hadd, bind_tc_ok, hinc, bind_tc_ok] at h
        have hnext : block1.val + n = 64 := by rw [hincVal]; omega
        exact ih block1 sum1 out hnext hsum1 hhigh hmask h
end AspisR1.TerminalV4ActiveLiteralLoopCanonical
