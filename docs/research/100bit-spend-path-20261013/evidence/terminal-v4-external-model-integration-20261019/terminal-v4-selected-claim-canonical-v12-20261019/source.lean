import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4QM31ExactV5
import SelectedClaimProofs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4SelectedClaimCanonicalV1
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Canonical := AspisR1.TerminalV4QM31Exact.CurrentCanonicalQM

theorem index_ok_canonical
    (claims : Array QM 84#usize) (index : Std.Usize) (value : QM)
    (hindex : Array.index_usize claims index = .ok value)
    (hclaims : ∀ i : Fin 84, Canonical (claims.val[i.val]'(by simpa [claims.property] using i.isLt))) :
    Canonical value := by
  unfold Array.index_usize at hindex
  cases hget : claims[index]? with
  | none => simp [hget] at hindex
  | some x =>
    have hlt : index.val < claims.val.length := by
      by_contra hn
      have hnone : claims.val[index.val]? = none :=
        List.getElem?_eq_none (Nat.not_lt.mp hn)
      have hcontr : claims[index]? = none := hnone
      rw [hcontr] at hget
      contradiction
    have hgetValue : claims.val[index.val]? = some (claims.val[index.val]'hlt) :=
      List.getElem?_eq_getElem hlt
    have hx : claims.val[index.val]'hlt = x :=
      Option.some.inj (hgetValue.symm.trans hget)
    simp only [hget] at hindex
    injection hindex with hv
    subst value
    have hcanon := hclaims ⟨index.val, by simpa [claims.property] using hlt⟩
    simpa [hx] using hcanon


theorem selected_claim_index_of_zero_point
    (claims : Array QM 84#usize) (column : Std.Usize) (value : QM)
    (hcolumn : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok column)
    (hclaim : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize column = .ok value) :
    Array.index_usize claims column = .ok value := by
  have hbase : ∃ base : Std.Usize,
      pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = .ok base := by
    unfold pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN at hcolumn
    cases hb : pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 with
    | ok base => exact ⟨base, hb⟩
    | fail err => simp [hb] at hcolumn
    | div => simp [hb] at hcolumn
  obtain ⟨base, hb⟩ := hbase
  unfold pool_v1.pair_forest_semantic_terminal.selected_claim at hclaim
  simp only [hb, bind_tc_ok] at hclaim
  -- With row point zero the checked index is exactly the selected column.
  simp at hclaim
  exact hclaim


theorem selected_h1_success_canonical_current
    (claims : Array QM 84#usize) (column : Std.Usize) (h1Z : QM)
    (hclaims : ∀ i : Fin 84, Canonical (claims.val[i.val]'(by simpa [claims.property] using i.isLt)))
    (hcolumn : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok column)
    (hclaim : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize column = .ok h1Z) :
    Canonical h1Z := by
  have hclaimsOld : ∀ i : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[i.val]'(by simpa [claims.property] using i.isLt)) := by
    intro i
    simpa [AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
      AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
      AspisR1.ExtractedMaskTowerAdd.P,
      AspisR1.ExtractedMaskM31AddSub.P,
      AspisR1.TerminalV4TowerAdd.CanonicalQM,
      AspisR1.TerminalV4TowerAdd.CanonicalCM,
      AspisR1.TerminalV4TowerAdd.P,
      AspisR1.TerminalV4M31AddSub.P] using hclaims i
  obtain ⟨q, hq, _hcell, hqcanon⟩ :=
    AspisR1SelectedMaskProbe.selected_h1_claim_success claims hclaimsOld
  have hdo : (do
      let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
      pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i) = .ok h1Z := by
    rw [hcolumn]
    simp only [bind_tc_ok]
    exact hclaim
  have hqeq : q = h1Z := by
    rw [hdo] at hq
    injection hq
  simpa [AspisR1.ExtractedMaskTowerAdd.CanonicalQM,
    AspisR1.ExtractedMaskTowerAdd.CanonicalCM,
    AspisR1.ExtractedMaskTowerAdd.P,
    AspisR1.ExtractedMaskM31AddSub.P,
    AspisR1.TerminalV4TowerAdd.CanonicalQM,
    AspisR1.TerminalV4TowerAdd.CanonicalCM,
    AspisR1.TerminalV4TowerAdd.P,
    AspisR1.TerminalV4M31AddSub.P, hqeq] using hqcanon

end AspisR1.TerminalV4SelectedClaimCanonicalV1
end
