import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
import AspisR1.TerminalV4SelectorMaskSumCanonical
import AspisR1.TerminalV4BindPairSuccess
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

def lowCell (s : Selectors) (i : Fin 16) : QM :=
  s.low.val[i.val]'(by simpa [s.low.property] using i.isLt)

def highCell (s : Selectors) (i : Fin 64) : QM :=
  s.high.val[i.val]'(by simpa [s.high.property] using i.isLt)

def maskStepOK (s : Selectors) : Prop :=
  ∀ (b : Usize), b.val < 64 →
    ∃ mask, Array.index_usize Masks b = .ok mask ∧
      (mask = 0#u16 ∨ ∃ q, mask ≠ 0#u16 ∧ SumMask s.low mask = .ok q ∧ Canonical q)

private theorem usize_add_one_success (b : Usize) (hb : b.val < 64) :
    ∃ b1 : Usize, UScalar.add b 1#usize = .ok b1 ∧ b1.val = b.val + 1 := by
  have hmax := Usize.cMax_bound_concrete.1
  have hsum : b.val + 1 ≤ Usize.max := by omega
  have hone : (1#usize).val = 1 := by scalar_tac
  have hchecked : (b + 1#usize : Result Usize) ⦃ z => z.val = b.val + 1 ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq, hone] using hsum
  obtain ⟨b1, heq, hv⟩ := WP.spec_imp_exists hchecked
  refine ⟨b1, ?_, hv⟩
  change (b + 1#usize : Result Usize) = .ok b1
  exact heq

theorem active_loop_good (n : Nat) (s : Selectors) (block : Usize) (sum out : QM)
    (hbound : block.val + n = 64)
    (hsum : Canonical sum)
    (hhigh : ∀ i : Fin 64, Canonical (highCell s i))
    (hlow : ∀ i : Fin 16, Canonical (lowCell s i))
    (hrun : Active s sum block = .ok out) : Canonical out := by
  induction n generalizing block sum out with
  | zero =>
      have hblock : block.val = 64 := by omega
      have hnot : ¬ block < 64#usize := by scalar_tac
      have h := hrun
      change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop s sum block = .ok out at h
      rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop.eq_def] at h
      simp only [if_neg hnot] at h
      have hout : out = sum := Result.ok.inj h.symm
      simpa [hout] using hsum
  | succ n ih =>
      have hb : block.val < 64 := by omega
      have hlt : block < 64#usize := by scalar_tac
      have hmaskBound : block.val < Masks.val.length := by simpa [Masks.property] using hb
      obtain ⟨mask, hmaskRead, _⟩ := WP.spec_imp_exists (Array.index_usize_spec Masks block hmaskBound)
      have h := hrun
      change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop s sum block = .ok out at h
      rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop.eq_def] at h
      simp only [if_pos hlt, hmaskRead, bind_tc_ok] at h
      obtain ⟨block1, hinc, hincVal⟩ := usize_add_one_success block hb
      by_cases hmaskZero : mask = 0#u16
      · have hmaskFalse : (mask != 0#u16) = false := by rw [hmaskZero]; decide
        simp only [hmaskFalse] at h
        simp only [if_neg (by decide : ¬ (false = true)), hinc, bind_tc_ok] at h
        change (do
          let block' ← UScalar.add block 1#usize
          Active s sum block') = .ok out at h
        simp only [hinc, bind_tc_ok] at h
        have hnext : block1.val + n = 64 := by rw [hincVal]; omega
        exact ih block1 sum out hnext hsum h
      · have hmaskTrue : (mask != 0#u16) = true := by simp [hmaskZero]
        have hhiRead : Array.index_usize s.high block = .ok (highCell s ⟨block.val, hb⟩) := by
          have hi : block.val < s.high.val.length := by simpa [s.high.property] using hb
          obtain ⟨q, hread, hval⟩ := WP.spec_imp_exists (Array.index_usize_spec s.high block hi)
          rw [hread]
          congr 1
        have hhi : Canonical (highCell s ⟨block.val, hb⟩) := hhigh ⟨block.val, hb⟩
        have hbranch := h
        simp only [hmaskTrue, if_true, hhiRead, bind_tc_ok] at hbranch
        obtain ⟨self1, sum1, hinner, htail⟩ :=
          AspisR1.TerminalV4BindPairSuccess.bind_pair_ok_inv
            (do
              let q1 ← SumMask s.low mask
              let q2 ← AspisR1SelectedMaskProbe.field.QM31.mul (highCell s ⟨block.val, hb⟩) q1
              let sum2 ← AspisR1SelectedMaskProbe.field.QM31.add sum q2
              ok (s, sum2))
            (fun self1 sum1 => do
              let block' ← UScalar.add block 1#usize
              Active self1 sum1 block') out hbranch
        obtain ⟨selected, hselected, hafter1⟩ :=
          AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
            (SumMask s.low mask)
            (fun q1 => do
              let q2 ← AspisR1SelectedMaskProbe.field.QM31.mul (highCell s ⟨block.val, hb⟩) q1
              let sum2 ← AspisR1SelectedMaskProbe.field.QM31.add sum q2
              ok (s, sum2)) (self1, sum1) hinner
        have hselectedCan := AspisR1.TerminalV4SelectorMaskSumCanonical.selector_mask_sum_success_canonical
          s.low mask selected hlow hselected
        obtain ⟨q2, hq2, hafter2⟩ :=
          AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
            (AspisR1SelectedMaskProbe.field.QM31.mul (highCell s ⟨block.val, hb⟩) selected)
            (fun q2 => do
              let sum2 ← AspisR1SelectedMaskProbe.field.QM31.add sum q2
              ok (s, sum2)) (self1, sum1) hafter1
        obtain ⟨sum2, hadd, hpairOut⟩ :=
          AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
            (AspisR1SelectedMaskProbe.field.QM31.add sum q2)
            (fun sum2 => ok (s, sum2)) (self1, sum1) hafter2
        have houtPair : (s, sum2) = (self1, sum1) := Result.ok.inj hpairOut
        have hself : self1 = s := (congrArg Prod.fst houtPair).symm
        have hsumEq : sum1 = sum2 := (congrArg Prod.snd houtPair).symm
        obtain ⟨prod, hmul, ⟨hprod, _⟩⟩ :=
          AspisR1.TerminalV4QM31MulCurrent.current_qm_mul_words
            (highCell s ⟨block.val, hb⟩) selected hhi hselectedCan
        have hprodEq : q2 = prod := Result.ok.inj (hq2.symm.trans hmul)
        have hq2Can : Canonical q2 := hprodEq ▸ hprod
        obtain ⟨sum2', hadd', hsum2', _⟩ :=
          AspisR1.TerminalV4TowerAdd.current_qm_add_mod sum q2 hsum hq2Can
        have hsum2Eq : sum2 = sum2' := Result.ok.inj (hadd.symm.trans hadd')
        have hsumNext : Canonical sum2 := hsum2Eq ▸ hsum2'
        rw [hself, hsumEq] at htail
        change (do
          let block' ← UScalar.add block 1#usize
          Active s sum2 block') = .ok out at htail
        simp only [hinc, bind_tc_ok] at htail
        have hnext : block1.val + n = 64 := by rw [hincVal]; omega
        exact ih block1 sum2 out hnext hsumNext htail
end AspisR1.TerminalV4ActiveLiteralLoopCanonical
