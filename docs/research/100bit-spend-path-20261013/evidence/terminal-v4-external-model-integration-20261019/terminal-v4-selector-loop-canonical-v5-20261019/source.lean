import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
open Aeneas Aeneas.Std Result ControlFlow Error WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.TerminalV4SelectorLoopCanonical
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
abbrev Canonical := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev Values := Array QM 16#usize
abbrev Loop := AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop

def valueCell (values : Values) (i : Fin 16) : QM :=
  values.val[i.val]'(by simpa [values.property] using i.isLt)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem index_success_bound {α : Type} (a : Array α 16#usize) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < a.val.length := by
  by_cases hi : i.val < a.val.length
  · exact hi
  · have hge : a.val.length ≤ i.val := Nat.le_of_not_gt hi
    unfold Array.index_usize at h
    have hnone : a.val[i.val]? = none := List.getElem?_eq_none_iff.mpr hge
    rw [hnone] at h
    cases h

private theorem mask_drop (mask i1 : U16)
    (hnz : mask ≠ 0#u16) (hsub : UScalar.sub mask 1#u16 = .ok i1) :
    (mask &&& i1).val < mask.val := by
  have hone : (1#u16).val = 1 := by scalar_tac
  have hpos : 1 ≤ mask.val := by
    by_contra hnot
    have hz : mask.val = 0 := by omega
    have heq : mask = 0#u16 := UScalar.eq_of_val_eq (by simpa using hz)
    exact hnz heq
  have hsubSpec : UScalar.sub mask 1#u16
      ⦃ z => z.val = mask.val - 1 ∧ 1 ≤ mask.val ⦄ := by
    apply UScalar.sub_spec
    rw [hone]
    omega
  obtain ⟨i1', heq, hpost⟩ := WP.spec_imp_exists hsubSpec
  have hsame : i1' = i1 := Result.ok.inj (heq.symm.trans hsub)
  have hval : i1.val = mask.val - 1 := by simpa [hsame] using hpost.1
  have hand : (mask &&& i1).val = mask.val &&& i1.val := UScalar.val_and mask i1
  have hle : mask.val &&& i1.val ≤ i1.val := Nat.and_le_right
  calc
    (mask &&& i1).val = mask.val &&& i1.val := hand
    _ ≤ i1.val := hle
    _ < mask.val := by omega

theorem loop_success_canonical (values : Values) (mask : U16) (complement : Bool)
    (sum out : QM)
    (hvalues : ∀ i : Fin 16, Canonical (valueCell values i))
    (hsum : Canonical sum)
    (hrun : Loop values mask complement sum = .ok out) : Canonical out := by
  suffices H : ∀ n, ∀ (mask : U16), mask.val = n → ∀ (sum out : QM), Canonical sum →
      Loop values mask complement sum = .ok out → Canonical out from
    H mask.val mask rfl sum out hsum hrun
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro current hcurrent sum out hsum hrun
      by_cases hzero : current = 0#u16
      · subst current
        have h := hrun
        change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop values
          (0#u16) complement sum = .ok out at h
        rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop.eq_def] at h
        simp only [if_neg (by decide : ¬ ((0#u16 != 0#u16) = true))] at h
        have hout : out = sum := Result.ok.inj h.symm
        simpa [hout] using hsum
      · have hnonzero : (current != 0#u16) = true := by
          have : current != 0#u16 := by simpa using hzero
          simp [this]
        have h := hrun
        change AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop values
          current complement sum = .ok out at h
        rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop.eq_def] at h
        simp only [hnonzero, if_true] at h
        obtain ⟨ti, htrail, hrest⟩ := bind_success _ _ _ h
        obtain ⟨index, hcast, hrest⟩ := bind_success _ _ _ hrest
        obtain ⟨q, hread, hrest⟩ := bind_success _ _ _ hrest
        have hidx := index_success_bound values index q hread
        have hvalue : Canonical (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) :=
          hvalues ⟨index.val, by simpa [values.property] using hidx⟩
        have hqeq : q = valueCell values ⟨index.val, by simpa [values.property] using hidx⟩ := by
          have hspec := Array.index_usize_spec values index hidx
          rw [hread] at hspec
          exact Result.ok.inj hspec
        subst q
        cases complement with
        | false =>
          obtain ⟨sum1, hadd, hsum1, _⟩ :=
            AspisR1.TerminalV4TowerAdd.current_qm_add_mod sum
              (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) hsum hvalue
          obtain ⟨i1, hsub, hrest⟩ := bind_success _ _ _ hrest
          have hne := mask_drop current i1 hzero hsub
          obtain ⟨mask1, hmask1, hrest⟩ := bind_success _ _ _ hrest
          have hmask1eq : mask1 = current &&& i1 := by
            simp only [lift] at hmask1
            exact Result.ok.inj hmask1
          have hnext : Loop values mask1 false sum1 = .ok out := by
            simpa only [hmask1eq] using hrest
          have hlt : mask1.val < n := by rw [hmask1eq, ← hcurrent]; exact hne
          exact ih mask1.val hlt mask1 rfl sum1 out hsum1 hnext
        | true =>
          obtain ⟨sum1, hsubfield, hsum1, _⟩ :=
            AspisR1.TerminalV4TowerAdd.current_qm_sub_mod sum
              (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) hsum hvalue
          obtain ⟨i1, hsub, hrest⟩ := bind_success _ _ _ hrest
          have hne := mask_drop current i1 hzero hsub
          obtain ⟨mask1, hmask1, hrest⟩ := bind_success _ _ _ hrest
          have hmask1eq : mask1 = current &&& i1 := by
            simp only [lift] at hmask1
            exact Result.ok.inj hmask1
          have hnext : Loop values mask1 true sum1 = .ok out := by
            simpa only [hmask1eq] using hrest
          have hlt : mask1.val < n := by rw [hmask1eq, ← hcurrent]; exact hne
          exact ih mask1.val hlt mask1 rfl sum1 out hsum1 hnext
end AspisR1.TerminalV4SelectorLoopCanonical
