import TerminalV4CompositionPartsCallerChunk07dV2
import TerminalV4QM31ExactV5

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


theorem selected_width_ok :
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = .ok 28#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  decide

theorem selected_h1_column_ok :
    pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok 26#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  decide

theorem selected_h1_success_canonical_current
    (claims : Array QM 84#usize) (column : Std.Usize) (h1Z : QM)
    (hclaims : ∀ i : Fin 84, Canonical (claims.val[i.val]'(by simpa [claims.property] using i.isLt)))
    (hcolumn : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok column)
    (hclaim : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize column = .ok h1Z) :
    Canonical h1Z := by
  have hcol : column = 26#usize := by
    have heq := hcolumn.symm.trans selected_h1_column_ok
    injection heq
  have hidx : Array.index_usize claims 26#usize = .ok h1Z := by
    unfold pool_v1.pair_forest_semantic_terminal.selected_claim at hclaim
    rw [selected_width_ok, hcol] at hclaim
    simp only [bind_tc_ok] at hclaim
    simpa using hclaim
  exact index_ok_canonical claims 26#usize h1Z hidx hclaims


end AspisR1.TerminalV4SelectedClaimCanonicalV1
end
