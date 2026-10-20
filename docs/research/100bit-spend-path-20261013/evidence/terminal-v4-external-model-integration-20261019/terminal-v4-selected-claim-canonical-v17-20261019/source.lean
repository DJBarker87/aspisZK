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


private theorem usize_add_eq_ok (a b out : Std.Usize)
    (hval : a.val + b.val = out.val)
    (hbound : a.val + b.val ≤ Usize.max) :
    UScalar.add a b = .ok out := by
  have hchecked : (a + b : Result Std.Usize) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hbound
  obtain ⟨x, hx, hxval⟩ := Aeneas.Std.WP.spec_imp_exists hchecked
  change (a + b : Result Std.Usize) = .ok out
  rw [hx]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hxval]
  exact hval

private theorem smallUsize_bound (n : Nat) (hn : n < 84) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hb : 84 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

theorem selected_width_ok :
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = .ok 28#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  change (do
    let i ← UScalar.add (16#usize) (10#usize)
    UScalar.add i (2#usize)) = .ok 28#usize
  have h1 : UScalar.add (16#usize) (10#usize) = .ok (26#usize) := by
    apply usize_add_eq_ok
    · scalar_tac
    · have hv : (16#usize).val + (10#usize).val = 26 := by norm_num
      rw [hv]
      have hn := smallUsize_bound 26 (by omega)
      rw [← Usize.max_succ_eq_pow] at hn
      omega
  rw [h1]
  simp only [bind_tc_ok]
  apply usize_add_eq_ok
  · scalar_tac
  · have hv : (26#usize).val + (2#usize).val = 28 := by norm_num
    rw [hv]
    have hn := smallUsize_bound 28 (by omega)
    rw [← Usize.max_succ_eq_pow] at hn
    omega

theorem selected_h1_column_ok :
    pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok 26#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  change UScalar.add (16#usize) (10#usize) = .ok 26#usize
  apply usize_add_eq_ok
  · scalar_tac
  · have hv : (16#usize).val + (10#usize).val = 26 := by norm_num
    rw [hv]
    have hn := smallUsize_bound 26 (by omega)
    rw [← Usize.max_succ_eq_pow] at hn
    omega

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
    have hmul : ((0#usize) * (28#usize) : Result Std.Usize) = .ok (0#usize) := by
      have hchecked : ((0#usize) * (28#usize) : Result Std.Usize)
          ⦃ x => x.val = (0#usize).val * (28#usize).val ⦄ := by
        apply UScalar.mul_spec
        scalar_tac
      obtain ⟨x, hx, hxv⟩ := Aeneas.Std.WP.spec_imp_exists hchecked
      have hxzero : x = 0#usize := by
        apply UScalar.eq_of_val_eq
        rw [hxv]
        scalar_tac
      simpa only [hxzero] using hx
    have hadd : UScalar.add (0#usize) (26#usize) = .ok (26#usize) := by
      apply usize_add_eq_ok
      · scalar_tac
      · have hv : (0#usize).val + (26#usize).val = 26 := by norm_num
        rw [hv]
        have hn := smallUsize_bound 26 (by omega)
        rw [← Usize.max_succ_eq_pow] at hn
        omega
    have haddOp : ((0#usize) + (26#usize) : Result Std.Usize) = .ok (26#usize) := hadd
    simp only [hmul, bind_tc_ok, haddOp, bind_tc_ok] at hclaim
    exact hclaim
  exact index_ok_canonical claims 26#usize h1Z hidx hclaims


end AspisR1.TerminalV4SelectedClaimCanonicalV1
end
