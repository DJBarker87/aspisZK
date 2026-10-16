import SelectedClaimSlice
import ExtractedMaskReducerOps
import ExtractedMaskTowerAdd
import ExtractedMaskHornerStep

/-! Proof-only adapter for the pinned, byte-exact G selected-claim slice. -/
set_option autoImplicit false

namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result ControlFlow

private theorem usize_add_eq_ok (a b out : Usize)
    (hval : a.val + b.val = out.val)
    (hbound : a.val + b.val ≤ Usize.max) :
    UScalar.add a b = .ok out := by
  have hchecked : (a + b : Result Usize) ⦃ x => x.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hbound
  obtain ⟨x, hx, hxval⟩ := Aeneas.Std.WP.spec_imp_exists hchecked
  change (a + b : Result Usize) = .ok out
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
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
      = .ok 28#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  change (do
    let i ← UScalar.add (16#usize) (10#usize)
    UScalar.add i (2#usize)) = .ok 28#usize
  have h1 : UScalar.add (16#usize) (10#usize) = .ok (26#usize) := by
    apply usize_add_eq_ok
    · scalar_tac
    · scalar_tac
  rw [h1]
  simp only [bind_tc_ok]
  apply usize_add_eq_ok
  · scalar_tac
  · scalar_tac

theorem selected_h1_column_ok :
    pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok 26#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  change UScalar.add (16#usize) (10#usize) = .ok 26#usize
  apply usize_add_eq_ok <;> scalar_tac

theorem selected_g_column_ok :
    pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN = .ok 27#usize := by
  unfold pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
  rw [selected_h1_column_ok]
  change (do let i ← (.ok 26#usize : Result Std.Usize); UScalar.add i (1#usize)) = .ok 27#usize
  simp only [bind_tc_ok]
  apply usize_add_eq_ok <;> scalar_tac

/-- Every bounded source selection is a successful checked array read at the
row-major index `point*28+column`; per-cell canonicality is inherited from the
actual caller-provided array. -/
theorem selected_claim_success
    (claims : Array field.QM31 84#usize) (point column : Std.Usize)
    (hp : point.val < 3) (hc : column.val < 28)
    (hcanonical : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(by simpa [claims.property] using j.isLt))) :
    ∃ q : field.QM31,
      pool_v1.pair_forest_semantic_terminal.selected_claim claims point column = .ok q ∧
      q = claims.val[point.val * 28 + column.val]'(by
        have hindex : point.val * 28 + column.val < 84 := by omega
        simpa [claims.property] using hindex) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q := by
  have hindexNat : point.val * 28 + column.val < 84 := by omega
  have hmulBound : point.val * 28 < 2 ^ Std.UScalarTy.Usize.numBits :=
    smallUsize_bound _ (by omega)
  obtain ⟨i1, hi1, hi1val⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success
      (ty := .Usize) (point.val * 28) hmulBound
  have hmul : UScalar.mul point (28#usize) = .ok i1 := by
    change UScalar.tryMk .Usize (point.val * (28#usize).val) = .ok i1
    simpa [hi1val] using hi1
  have haddBound : i1.val + column.val < 2 ^ Std.UScalarTy.Usize.numBits :=
    smallUsize_bound _ (by rw [hi1val]; exact hindexNat)
  obtain ⟨i2, hi2, hi2val⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success
      (ty := .Usize) (i1.val + column.val) haddBound
  have hadd : UScalar.add i1 column = .ok i2 := by
    change UScalar.tryMk .Usize (i1.val + column.val) = .ok i2
    exact hi2
  have h84 : (84#usize).val = 84 := by scalar_tac
  have hreadBound : i2.val < (84#usize).val := by
    rw [hi2val, hi1val, h84]
    exact hindexNat
  have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok claims i2 hreadBound
  have hmulOp : (point * (28#usize) : Result Usize) = .ok i1 := by
    change UScalar.mul point (28#usize) = .ok i1
    exact hmul
  have haddOp : (i1 + column : Result Usize) = .ok i2 := hadd
  have hvalue : i2.val = point.val * 28 + column.val := by
    rw [hi2val, hi1val]
  refine ⟨claims.val[i2.val]'(by simpa [claims.property] using hreadBound), ?_, ?_, ?_⟩
  · simp only [pool_v1.pair_forest_semantic_terminal.selected_claim,
      selected_width_ok, bind_tc_ok]
    simp only [hmulOp, haddOp, bind_tc_ok, hread]
  · simpa [hvalue]
  · exact hcanonical ⟨i2.val, hreadBound⟩


/-- Composition's H1 selection from the first 28-column row. -/
theorem selected_h1_claim_success
    (claims : Array field.QM31 84#usize)
    (hcanonical : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(by simpa [claims.property] using j.isLt))) :
    ∃ q,
      (do
        let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
        pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i) = .ok q ∧
      q = claims.val[26]'(by simpa [claims.property] using (show 26 < 84 by norm_num)) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q := by
  obtain ⟨q, hq, hval, hcan⟩ := selected_claim_success claims 0#usize 26#usize
    (by norm_num) (by norm_num) hcanonical
  refine ⟨q, ?_, hval, hcan⟩
  simpa only [selected_h1_column_ok, bind_tc_ok] using hq

theorem selected_g_claim_success
    (claims : Array field.QM31 84#usize)
    (hcanonical : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(by simpa [claims.property] using j.isLt))) :
    ∃ q,
      (do
        let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
        pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i) = .ok q ∧
      q = claims.val[27]'(by simpa [claims.property] using (show 27 < 84 by norm_num)) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q := by
  obtain ⟨q, hq, hval, hcan⟩ := selected_claim_success claims 0#usize 27#usize
    (by norm_num) (by norm_num) hcanonical
  refine ⟨q, ?_, hval, hcan⟩
  simpa only [selected_g_column_ok, bind_tc_ok] using hq

/-- Source call_mut succeeds for every flat index below 84, and returns the
row-major cell with quotient/remainder by 28. -/
theorem terminal_flat_call_mut_success
    (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
    (flat : Std.Usize) (hflat : flat.val < 84)
    (hcanonical : ∀ p : Fin 3, ∀ col : Fin 28,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        ((c.val[p.val]'(by
            have h3p : (3#usize : Std.Usize).val = 3 := by scalar_tac
            rw [c.property, h3p]
            exact p.isLt)).val[
          col.val]'(by
            have h29p : (29#usize : Std.Usize).val = 29 := by scalar_tac
            rw [((c.val[p.val]'(by
              have h3p : (3#usize : Std.Usize).val = 3 := by scalar_tac
              rw [c.property, h3p]
              exact p.isLt)).property), h29p]
            omega))) :
    ∃ q : field.QM31,
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        c flat = .ok (q, c) ∧
      let row := c.val[(flat.val / 28)]' (by
        have hquot : flat.val / 28 < 3 := by omega
        simpa [c.property] using hquot)
      q = row.val[flat.val % 28]' (by
        have hcol28 : flat.val % 28 < 28 := by omega
        have hcol29 : flat.val % 28 < 29 := by omega
        simpa [row.property] using hcol29) ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q := by
  have h28 : (28#usize : Std.Usize).val = 28 := by scalar_tac
  have hden : (28#usize : Std.Usize).val ≠ 0 := by rw [h28]; omega
  obtain ⟨row, hdiv, hdivVal⟩ := @UScalar.div_spec .Usize flat (28#usize) hden
  have hmodSpec := UScalar.rem_spec flat (y := 28#usize) hden
  obtain ⟨col, hmodWp, hmodVal⟩ := Aeneas.Std.WP.spec_imp_exists hmodSpec
  have hmod : UScalar.rem flat (28#usize) = .ok col := by
    simpa [HMod.hMod] using hmodWp
  have hrow : row.val < 3 := by rw [hdivVal, h28]; omega
  have hcol : col.val < 28 := by rw [hmodVal, h28]; exact Nat.mod_lt _ (by omega)
  have hvquot : row.val = flat.val / 28 := by simpa [h28] using hdivVal
  have hvrem : col.val = flat.val % 28 := by simpa [h28] using hmodVal
  have hquot : flat.val / 28 < 3 := by calc
    flat.val / 28 = row.val := hvquot.symm
    _ < 3 := hrow
  have hrem : flat.val % 28 < 28 := by calc
    flat.val % 28 = col.val := hvrem.symm
    _ < 28 := hcol
  have h3 : (3#usize : Std.Usize).val = 3 := by scalar_tac
  have h29 : (29#usize : Std.Usize).val = 29 := by scalar_tac
  have hrowRead := @AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    (Array field.QM31 29#usize) (3#usize) c row (by
    rw [h3]
    exact hrow)
  have hrowIndex : row.val < c.val.length := by
    rw [c.property, h3]
    exact hrow
  let r := c.val[row.val]'hrowIndex
  have hcolRead := @AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
    field.QM31 (29#usize) r col (by
    rw [h29]
    omega)
  have hqBound : flat.val % 28 < r.val.length := by
    have hb : flat.val % 28 < (29#usize).val := by rw [h29]; omega
    simpa [r.property] using hb
  let rowResult := c.val[flat.val / 28]'(by
    have h3q : (3#usize : Std.Usize).val = 3 := by scalar_tac
    rw [c.property, h3q]
    exact hquot)
  have hr : r = rowResult := by
    dsimp [r, rowResult]
    congr 1
  refine ⟨rowResult.val[flat.val % 28]'(by
    have hb : flat.val % 28 < (29#usize).val := by rw [h29]; omega
    simpa [rowResult.property] using hb), ?_, ?_, ?_⟩
  · simp only [pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
      hdiv, hmodWp, bind_tc_ok]
    rw [hrowRead]
    change (do
      let q ← Array.index_usize r col
      ok (q, c)) = ok (rowResult.val[flat.val % 28]'(by
        have hb : flat.val % 28 < (29#usize).val := by rw [h29]; omega
        simpa [rowResult.property] using hb), c)
    rw [hcolRead]
    congr 1
    simpa [hr, hvrem]
  · rfl
  · exact hcanonical ⟨flat.val / 28, hquot⟩ ⟨flat.val % 28, hrem⟩

#print axioms selected_width_ok
#print axioms selected_h1_column_ok
#print axioms selected_g_column_ok
#print axioms selected_claim_success
#print axioms selected_h1_claim_success
#print axioms selected_g_claim_success
#print axioms terminal_flat_call_mut_success

end AspisR1SelectedMaskProbe
