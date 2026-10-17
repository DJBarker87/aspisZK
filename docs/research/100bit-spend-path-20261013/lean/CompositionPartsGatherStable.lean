import CompositionPartsGatherSlice
import SelectedClaimProofs
import ArrayFromFnCopyStable
import ExtractedMaskReducerOps
import SelectedClaimGatherSlice

/-! Exact source-callback gather facts for the four selected arrays made by
`composition_parts`. The underlying claims array is already the 84-cell flat
array. This does not prove that a successful `composition_parts` call reaches
these reads; it records the component-level gather contracts. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

private def flatCell (claims : Array field.QM31 84#usize) (n : Nat) : field.QM31 :=
  claims.val.getD n field.QM31.ZERO

private theorem flatCell_eq_get (claims : Array field.QM31 84#usize)
    (n : Nat) (hn : n < 84) :
    flatCell claims n = claims.val[n]'(by simpa [claims.property] using hn) := by
  have hlen : n < claims.val.length := by simpa [claims.property] using hn
  simp only [flatCell, List.getD_eq_getElem _ _ hlen]

private theorem claim_index_bound (claims : Array field.QM31 84#usize)
    (n : Nat) (hn : n < 84) : n < claims.val.length := by
  simpa [claims.property] using hn

private theorem smallUsizeBound (n : Nat) (hn : n < 84) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hb : 84 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

private theorem add16_success (i : Std.Usize) (hi : i.val < 10) :
    ∃ j : Std.Usize, (16#usize + i : Result Std.Usize) = .ok j ∧ j.val = 16 + i.val := by
  have hbound : 16 + i.val < 2 ^ Std.UScalarTy.Usize.numBits :=
    smallUsizeBound _ (by omega)
  obtain ⟨j, hj, hjval⟩ :=
    AspisR1.ExtractedMaskReducerOps.tryMk_success (ty := .Usize) (16 + i.val) hbound
  have hadd : (16#usize + i : Result Std.Usize) = .ok j := by
    change UScalar.tryMk .Usize (16 + i.val) = .ok j
    exact hj
  exact ⟨j, hadd, hjval⟩

/-- The first three source gathers select columns `0..15` from rows `0,1,2`.
All callback reads succeed, retain their flat claims capture, and therefore the
`from_fn` copy results equal the corresponding selected cells. -/
theorem first_three_gathers
    (claims : Array field.QM31 84#usize)
    (hcanonical : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(by simpa [claims.property] using j.isLt))) :
    (∃ z : Array field.QM31 16#usize,
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok z ∧
      (∀ i : Fin 16, z.val[i.val]'(by simpa [z.property] using i.isLt) =
        claims.val[i.val]'(claim_index_bound claims i.val (by omega))) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (z.val[i.val]'(by simpa [z.property] using i.isLt)))) ∧
    (∃ z : Array field.QM31 16#usize,
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok z ∧
      (∀ i : Fin 16, z.val[i.val]'(by simpa [z.property] using i.isLt) =
        claims.val[28 + i.val]'(claim_index_bound claims (28 + i.val) (by omega))) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (z.val[i.val]'(by simpa [z.property] using i.isLt)))) ∧
    (∃ z : Array field.QM31 16#usize,
      array_from_fn_copy 16#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok z ∧
      (∀ i : Fin 16, z.val[i.val]'(by simpa [z.property] using i.isLt) =
        claims.val[56 + i.val]'(claim_index_bound claims (56 + i.val) (by omega))) ∧
      (∀ i : Fin 16, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (z.val[i.val]'(by simpa [z.property] using i.isLt)))) := by
  let value0 : Nat → field.QM31 := flatCell claims
  let inst0 := AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  have stable0 : ∀ i : Std.Usize, i.val < (16#usize).val →
      inst0.call_mut claims i = .ok (value0 i.val, claims) := by
    intro i hi
    have hi16 : i.val < 16 := by scalar_tac
    have hi28 : i.val < 28 := by omega
    obtain ⟨q, hq, hvalue, _⟩ := selected_claim_success claims 0#usize i (by norm_num) hi28 hcanonical
    have hflat : q = value0 i.val := by
      dsimp [value0]
      rw [flatCell_eq_get claims i.val (by omega)]
      simpa using hvalue
    simpa [inst0, AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut, hq, hflat]
  obtain ⟨z0, hz0, cells0⟩ := array_from_fn_copy_stable
    (16#usize) AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy inst0 field.QM31.ZERO claims value0 stable0
  let value1 : Nat → field.QM31 := fun n => flatCell claims (28 + n)
  let inst1 := AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  have stable1 : ∀ i : Std.Usize, i.val < (16#usize).val →
      inst1.call_mut claims i = .ok (value1 i.val, claims) := by
    intro i hi
    have hi16 : i.val < 16 := by scalar_tac
    have hi28 : i.val < 28 := by omega
    obtain ⟨q, hq, hvalue, _⟩ := selected_claim_success claims 1#usize i (by norm_num) hi28 hcanonical
    have hflat : q = value1 i.val := by
      dsimp [value1]
      rw [flatCell_eq_get claims (28 + i.val) (by omega)]
      simpa using hvalue
    simpa [inst1, AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut, hq, hflat]
  obtain ⟨z1, hz1, cells1⟩ := array_from_fn_copy_stable
    (16#usize) AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy inst1 field.QM31.ZERO claims value1 stable1
  let value2 : Nat → field.QM31 := fun n => flatCell claims (56 + n)
  let inst2 := AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  have stable2 : ∀ i : Std.Usize, i.val < (16#usize).val →
      inst2.call_mut claims i = .ok (value2 i.val, claims) := by
    intro i hi
    have hi16 : i.val < 16 := by scalar_tac
    have hi28 : i.val < 28 := by omega
    obtain ⟨q, hq, hvalue, _⟩ := selected_claim_success claims 2#usize i (by norm_num) hi28 hcanonical
    have hflat : q = value2 i.val := by
      dsimp [value2]
      rw [flatCell_eq_get claims (56 + i.val) (by omega)]
      simpa using hvalue
    simpa [inst2, AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut, hq, hflat]
  obtain ⟨z2, hz2, cells2⟩ := array_from_fn_copy_stable
    (16#usize) AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy inst2 field.QM31.ZERO claims value2 stable2
  have h16 : (16#usize).val = 16 := by scalar_tac
  refine ⟨⟨z0, hz0, ?_, ?_⟩, ⟨z1, hz1, ?_, ?_⟩, ⟨z2, hz2, ?_, ?_⟩⟩
  · intro i
    have hi := i.isLt
    have h := cells0 i.val (by rw [h16]; exact hi)
    have hv : value0 i.val = claims.val[i.val]'(claim_index_bound claims i.val (by omega)) := by
      dsimp [value0]
      exact flatCell_eq_get claims i.val (by omega)
    exact h.trans hv
  · intro i
    have hi := i.isLt
    have h := cells0 i.val (by rw [h16]; exact hi)
    rw [h]
    dsimp [value0]
    rw [flatCell_eq_get claims i.val (by omega)]
    exact hcanonical ⟨i.val, by omega⟩
  · intro i
    have hi := i.isLt
    have h := cells1 i.val (by rw [h16]; exact hi)
    have hv : value1 i.val = claims.val[28 + i.val]'(claim_index_bound claims (28 + i.val) (by omega)) := by
      dsimp [value1]
      exact flatCell_eq_get claims (28 + i.val) (by omega)
    exact h.trans hv
  · intro i
    have hi := i.isLt
    have h := cells1 i.val (by rw [h16]; exact hi)
    rw [h]
    dsimp [value1]
    rw [flatCell_eq_get claims (28 + i.val) (by omega)]
    exact hcanonical ⟨28 + i.val, by omega⟩
  · intro i
    have hi := i.isLt
    have h := cells2 i.val (by rw [h16]; exact hi)
    have hv : value2 i.val = claims.val[56 + i.val]'(claim_index_bound claims (56 + i.val) (by omega)) := by
      dsimp [value2]
      exact flatCell_eq_get claims (56 + i.val) (by omega)
    exact h.trans hv
  · intro i
    have hi := i.isLt
    have h := cells2 i.val (by rw [h16]; exact hi)
    rw [h]
    dsimp [value2]
    rw [flatCell_eq_get claims (56 + i.val) (by omega)]
    exact hcanonical ⟨56 + i.val, by omega⟩

/-- The separate mask-only gather selects columns 16 through 25 in row zero. -/
theorem mask_only_gather
    (claims : Array field.QM31 84#usize)
    (hcanonical : ∀ j : Fin 84,
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (claims.val[j.val]'(claim_index_bound claims j.val (by omega)))) :
    ∃ z : Array field.QM31 10#usize,
      array_from_fn_copy 10#usize AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy
        AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO claims = .ok z ∧
      (∀ i : Fin 10, z.val[i.val]'(by simpa [z.property] using i.isLt) =
        claims.val[16 + i.val]'(claim_index_bound claims (16 + i.val) (by omega))) ∧
      (∀ i : Fin 10, AspisR1.ExtractedMaskTowerAdd.CanonicalQM
        (z.val[i.val]'(by simpa [z.property] using i.isLt))) := by
  let value : Nat → field.QM31 := fun n => flatCell claims (16 + n)
  let inst := AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  have stable : ∀ i : Std.Usize, i.val < (10#usize).val →
      inst.call_mut claims i = .ok (value i.val, claims) := by
    intro i hi
    have hi10 : i.val < 10 := by scalar_tac
    obtain ⟨j, hadd, hjval⟩ := add16_success i hi10
    obtain ⟨q, hq, hvalue, _⟩ := selected_claim_success claims 0#usize j
      (by norm_num) (by rw [hjval]; omega) hcanonical
    have hflat : q = value i.val := by
      dsimp [value]
      rw [flatCell_eq_get claims (16 + i.val) (by omega)]
      have hvalue': q = claims.val[16 + i.val]'(by simpa [claims.property] using show 16 + i.val < 84 by omega) := by
        simpa [hjval] using hvalue
      exact hvalue'
    simp only [inst, AspisR1CompositionPartsGatherCut.pool_v1.pair_forest_semantic_terminal.composition_parts.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut,
      pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1,
      hadd, bind_tc_ok, hq, hflat]
  obtain ⟨z, hz, cells⟩ := array_from_fn_copy_stable
    (10#usize) AspisR1CompositionPartsGatherCut.field.QM31.Insts.CoreMarkerCopy inst field.QM31.ZERO claims value stable
  have h10 : (10#usize).val = 10 := by scalar_tac
  refine ⟨z, hz, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    have h := cells i.val (by rw [h10]; exact hi)
    have hv : value i.val = claims.val[16 + i.val]'(claim_index_bound claims (16 + i.val) (by omega)) := by
      dsimp [value]
      exact flatCell_eq_get claims (16 + i.val) (by omega)
    exact h.trans hv
  · intro i
    have hi := i.isLt
    have h := cells i.val (by rw [h10]; exact hi)
    rw [h]
    dsimp [value]
    rw [flatCell_eq_get claims (16 + i.val) (by omega)]
    exact hcanonical ⟨16 + i.val, by omega⟩

#print axioms first_three_gathers
#print axioms mask_only_gather
end AspisR1SelectedMaskProbe
