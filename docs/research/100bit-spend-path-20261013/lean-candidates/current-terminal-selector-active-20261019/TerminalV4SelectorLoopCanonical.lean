import TerminalV4ActiveLiteralClosureV2
import TerminalV4TowerAddV2
import TerminalV4QM31MulCurrent
import AspisR1.TerminalV4ResultAndIndexSuccess
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
  by_cases hi : i.val < a.val.length
  · exact hi
  · have hge : a.val.length ≤ i.val := Nat.le_of_not_gt hi
    unfold Array.index_usize at h
    change (match a.val[i.val]? with | none => Result.fail Error.arrayOutOfBounds | some y => Result.ok y) = .ok x at h
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

private theorem read_add_success_canonical (values : Values) (index : Usize)
    (sum out : QM) (hvalues : ∀ i : Fin 16, Canonical (valueCell values i))
    (hsum : Canonical sum)
    (hrun : (do
      let q ← Array.index_usize values index
      AspisR1SelectedMaskProbe.field.QM31.add sum q) = .ok out) : Canonical out := by
  obtain ⟨q, hread, hadd⟩ :=
    AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
      (Array.index_usize values index)
      (fun q => AspisR1SelectedMaskProbe.field.QM31.add sum q) out hrun
  have hidx := AspisR1.TerminalV4ResultAndIndexSuccess.array_index_ok_lt values index q hread
  obtain ⟨q', hreadSpec, hvalueEq⟩ := WP.spec_imp_exists (Array.index_usize_spec values index hidx)
  have hqeq : q = q' := Result.ok.inj (hread.symm.trans hreadSpec)
  have hcell : q = valueCell values ⟨index.val, by simpa [values.property] using hidx⟩ := hqeq.trans hvalueEq
  have hvalue : Canonical (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) :=
    hvalues ⟨index.val, by simpa [values.property] using hidx⟩
  obtain ⟨out', hadd', hout', _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_qm_add_mod sum
      (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) hsum hvalue
  have hactual : AspisR1SelectedMaskProbe.field.QM31.add sum
      (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) = .ok out := by
    rw [← hcell]
    exact hadd
  have heq : out = out' := Result.ok.inj (hactual.symm.trans hadd')
  simpa [heq] using hout'

private theorem read_sub_success_canonical (values : Values) (index : Usize)
    (sum out : QM) (hvalues : ∀ i : Fin 16, Canonical (valueCell values i))
    (hsum : Canonical sum)
    (hrun : (do
      let q ← Array.index_usize values index
      AspisR1SelectedMaskProbe.field.QM31.sub sum q) = .ok out) : Canonical out := by
  obtain ⟨q, hread, hsub⟩ :=
    AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
      (Array.index_usize values index)
      (fun q => AspisR1SelectedMaskProbe.field.QM31.sub sum q) out hrun
  have hidx := AspisR1.TerminalV4ResultAndIndexSuccess.array_index_ok_lt values index q hread
  obtain ⟨q', hreadSpec, hvalueEq⟩ := WP.spec_imp_exists (Array.index_usize_spec values index hidx)
  have hqeq : q = q' := Result.ok.inj (hread.symm.trans hreadSpec)
  have hcell : q = valueCell values ⟨index.val, by simpa [values.property] using hidx⟩ := hqeq.trans hvalueEq
  have hvalue : Canonical (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) :=
    hvalues ⟨index.val, by simpa [values.property] using hidx⟩
  obtain ⟨out', hsub', hout', _⟩ :=
    AspisR1.TerminalV4TowerAdd.current_qm_sub_mod sum
      (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) hsum hvalue
  have hactual : AspisR1SelectedMaskProbe.field.QM31.sub sum
      (valueCell values ⟨index.val, by simpa [values.property] using hidx⟩) = .ok out := by
    rw [← hcell]
    exact hsub
  have heq : out = out' := Result.ok.inj (hactual.symm.trans hsub')
  simpa [heq] using hout'

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
        obtain ⟨ti, htrail, hrest⟩ := AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv _ _ _ h
        obtain ⟨index, hcast, hrest⟩ := AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv _ _ _ hrest
        cases complement with
        | false =>
          simp only [if_neg (by decide : ¬ (false = true))] at hrest
          obtain ⟨sum1, hcompound, htail⟩ :=
            AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
              (do
                let q ← Array.index_usize values index
                AspisR1SelectedMaskProbe.field.QM31.add sum q)
              (fun sum1 => do
                let i1 ← UScalar.sub current 1#u16
                let mask1 ← lift (current &&& i1)
                Loop values mask1 false sum1) out hrest
          have hsum1 := read_add_success_canonical values index sum sum1 hvalues hsum hcompound
          obtain ⟨i1, hsub, htail⟩ :=
            AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
              (UScalar.sub current 1#u16)
              (fun i1 => do
                let mask1 ← lift (current &&& i1)
                Loop values mask1 false sum1) out htail
          have hne := mask_drop current i1 hzero hsub
          have hnext : Loop values (current &&& i1) false sum1 = .ok out := by
            simpa only [lift, bind_tc_ok] using htail
          have hlt : (current &&& i1).val < n := by rw [← hcurrent]; exact hne
          exact ih (current &&& i1).val hlt (current &&& i1) rfl sum1 out hsum1 hnext
        | true =>
          simp only [if_pos rfl, if_true] at hrest
          obtain ⟨sum1, hcompound, htail⟩ :=
            AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
              (do
                let q ← Array.index_usize values index
                AspisR1SelectedMaskProbe.field.QM31.sub sum q)
              (fun sum1 => do
                let i1 ← UScalar.sub current 1#u16
                let mask1 ← lift (current &&& i1)
                Loop values mask1 true sum1) out hrest
          have hsum1 := read_sub_success_canonical values index sum sum1 hvalues hsum hcompound
          obtain ⟨i1, hsub, htail⟩ :=
            AspisR1.TerminalV4ResultAndIndexSuccess.bind_ok_inv
              (UScalar.sub current 1#u16)
              (fun i1 => do
                let mask1 ← lift (current &&& i1)
                Loop values mask1 true sum1) out htail
          have hne := mask_drop current i1 hzero hsub
          have hnext : Loop values (current &&& i1) true sum1 = .ok out := by
            simpa only [lift, bind_tc_ok] using htail
          have hlt : (current &&& i1).val < n := by rw [← hcurrent]; exact hne
          exact ih (current &&& i1).val hlt (current &&& i1) rfl sum1 out hsum1 hnext
end AspisR1.TerminalV4SelectorLoopCanonical
