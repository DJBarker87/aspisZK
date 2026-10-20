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

private theorem index_success_bound {α : Type} (a : Array α 16#usize) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < a.val.length := by
  by_contra hnot
  have hge : a.val.length ≤ i.val := Nat.le_of_not_gt hnot
  unfold Array.index_usize at h
  simp [hge] at h

private theorem mask_drop (mask i1 : U16)
    (hnz : mask ≠ 0#u16) (hsub : UScalar.sub mask 1#u16 = .ok i1) :
    (mask &&& i1).val < mask.val := by
  have hone : (1#u16).val = 1 := by scalar_tac
  have hsubSpec : UScalar.sub mask 1#u16
      ⦃ z => z.val = mask.val - 1 ∧ 1 ≤ mask.val ⦄ := by
    apply UScalar.sub_spec
    rw [hone]
    have hval : 0 < mask.val := by
      intro hzero
      have : mask.val = (0#u16).val := by simpa using hzero
      have : mask = 0#u16 := UScalar.eq_of_val_eq this
      exact hnz this
    omega
  obtain ⟨i1', heq, hpost⟩ := WP.spec_imp_exists hsubSpec
  have hsame : i1' = i1 := Result.ok.inj (heq.symm.trans hsub)
  have hval : i1.val = mask.val - 1 := by simpa [hsame] using hpost.1
  have honeq : 1 ≤ mask.val := hpost.2
  have hand := UScalar.val_and mask i1
  omega

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
        change Loop values (0#u16) complement sum = .ok out at h
        rw [Loop.eq_def] at h
        simp only [if_neg (by decide : ¬ ((0#u16 != 0#u16) = true))] at h
        have hout : out = sum := Result.ok.inj h.symm
        simpa [hout] using hsum
      · have hnonzero : (current != 0#u16) = true := by
          have : current != 0#u16 := by simpa using hzero
          simp [this]
        have h := hrun
        change Loop values current complement sum = .ok out at h
        rw [Loop.eq_def] at h
        simp only [hnonzero, if_true] at h
        cases htrail : core.num.U16.trailing_zeros current with
        | fail e => simp only [htrail] at h
        | ok ti =>
          cases hcast : UScalar.cast UScalarTy.Usize ti with
          | fail e => simp only [hcast] at h
          | ok index =>
            cases hread : Array.index_usize values index with
            | fail e => simp only [hread] at h
            | ok q =>
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
                cases hsub : UScalar.sub current 1#u16 with
                | fail e => simp only [htrail, hcast, hread, if_neg (by decide : ¬ (false = true)), hsub] at h
                | ok i1 =>
                  have hne := mask_drop current i1 hzero hsub
                  simp only [htrail, hcast, hread, if_neg (by decide : ¬ (false = true)), hadd,
                    hsub, lift, bind_tc_ok] at h
                  have hnext : Loop values (current &&& i1) false sum1 = .ok out := h
                  have ih' := ih (current &&& i1).val (by
                    rw [UScalar.val_and]
                    exact hne) (current &&& i1) rfl sum1 out hsum1 hnext
                  exact ih'
              | true =>
                obtain ⟨sum1, hsubfield, hsum1, _⟩ :=
                  AspisR1.TerminalV4TowerAdd.current_qm_sub_mod sum
                    (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) hsum hvalue
                cases hsub : UScalar.sub current 1#u16 with
                | fail e => simp only [htrail, hcast, hread, if_pos (by decide : true = true), hsubfield, hsub] at h
                | ok i1 =>
                  have hne := mask_drop current i1 hzero hsub
                  simp only [htrail, hcast, hread, if_pos (by decide : true = true), hsubfield,
                    hsub, lift, bind_tc_ok] at h
                  have hnext : Loop values (current &&& i1) true sum1 = .ok out := h
                  have ih' := ih (current &&& i1).val (by
                    rw [UScalar.val_and]
                    exact hne) (current &&& i1) rfl sum1 out hsum1 hnext
                  exact ih'
end AspisR1.TerminalV4SelectorLoopCanonical
