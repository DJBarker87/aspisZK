import TerminalV4CompositionPartsTwoFoldCanonicalV1
import TerminalV4CompositionPartsContinueChunk07cV1
import AspisR1.TerminalV4CompositionCallerContinueExtractV8

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionCallerCanonicalV5
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

theorem index_ok_canonical
    (claims : Array QM 84#usize) (index : Std.Usize) (value : QM)
    (hindex : Array.index_usize claims index = .ok value)
    (hclaims : ∀ i : Fin 84, CanonicalQM (claims.val[i.val]'(by simpa [claims.property] using i.isLt))) :
    CanonicalQM value := by
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
      rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow] at hn
      omega
  rw [h1]
  simp only [bind_tc_ok]
  apply usize_add_eq_ok
  · scalar_tac
  · have hv : (26#usize).val + (2#usize).val = 28 := by norm_num
    rw [hv]
    have hn := smallUsize_bound 28 (by omega)
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow] at hn
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
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow] at hn
    omega

theorem selected_h1_success_canonical_current
    (claims : Array QM 84#usize) (column : Std.Usize) (h1Z : QM)
    (hclaims : ∀ i : Fin 84, CanonicalQM (claims.val[i.val]'(by simpa [claims.property] using i.isLt)))
    (hcolumn : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok column)
    (hclaim : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize column = .ok h1Z) :
    CanonicalQM h1Z := by
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
        rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow] at hn
        omega
    have haddOp : ((0#usize) + (26#usize) : Result Std.Usize) = .ok (26#usize) := hadd
    simp only [hmul, bind_tc_ok, haddOp, bind_tc_ok] at hclaim
    exact hclaim
  exact index_ok_canonical claims 26#usize h1Z hidx hclaims


/-- A successful execution of the generated continuation returns a canonical
composition result, given the exact successful calls made by the continuation
and pointwise canonicality of the two callback arrays and copy residual. -/
theorem caller_success_composition_and_h1_canonical_currentTower
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (claims : Array QM 84#usize)
    (point : Array QM 10#usize) (lambda chi theta : QM)
    (a a1 a2 : Array QM 16#usize) (maskOnly : Array QM 10#usize)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
    (poseidon : Aeneas.Std.Array QM 4#usize)
    (semantic : Aeneas.Std.Array QM 24#usize)
    (h1Z : QM) (pvpfcvv : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (iH iG : Std.Usize) (composition : QM) (c1 : Array QM 16#usize)
    (mask : Array QM 10#usize) (g copyActive : QM)
    (htheta : CanonicalQM theta) (hseed : CanonicalQM copy.residual)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt)))
    (hposeidonCanonical : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)))
    (hA : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims = .ok a)
    (hA1 : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims = .ok a1)
    (hA2 : array_from_fn_copy 16#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims = .ok a2)
    (hMask : array_from_fn_copy 10#usize field.QM31.Insts.CoreMarkerCopy
      pool_v1.pair_forest_semantic_terminal.composition_parts.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      field.QM31.ZERO claims = .ok maskOnly)
    (hselectors : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hsops : pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors = .ok sops)
    (hposeidon : poseidonEval { z := a, succ_z := a1, xor12_z := a2 } sops = .ok poseidon)
    (hsemantic : semanticEval { public1 with withdrawal_amount := public1.withdrawal_amount }
      { z := a, succ_z := a1, xor12_z := a2 } selectors = .ok semantic)
    (hI1 : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok iH)
    (hclaim1 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iH = .ok h1Z)
    (hclaims : ∀ i : Fin 84, CanonicalQM (claims.val[i.val]'(by simpa [claims.property] using i.isLt)))
    (hcopyVariant : pool_v1.pair_forest_semantic_terminal.copy_variant public1.variant = .ok pvpfcvv)
    (hcopy : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1Z
      selectors lambda chi public1.transition.live_snapshot.next_pair_index pvpfcvv = .ok copy)
    (hI2 : pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN = .ok iG)
    (hclaim2 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iG = .ok g)
    (hcaller : pool_v1.pair_forest_semantic_terminal.composition_parts_with_callers
      poseidonEval semanticEval public1 claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, c1, mask, g, h1Z, copyActive))) :
    CanonicalQM composition ∧ CanonicalQM h1Z := by
  obtain ⟨o, ho, hcontinue⟩ :=
    AspisR1.TerminalV4CompositionCallerContinueExtractV8.caller_success_extracts_continue
      poseidonEval semanticEval public1 claims point lambda chi theta composition c1 mask g h1Z copyActive hcaller
  have hsemanticActual : semanticEval { public1 with withdrawal_amount := o }
      { z := a, succ_z := a1, xor12_z := a2 } selectors = .ok semantic := by
    rw [ho]
    exact hsemantic
  obtain ⟨prepared, hnew, middle, hloop0, hmiddleCanonical, out, hloop1, houtCanonical⟩ :=
    AspisR1.TerminalV4CompositionPartsTwoFoldCanonical.composition_parts_two_folds_after_prepared_new
      semantic poseidon theta copy.residual htheta hseed hsemanticCanonical hposeidonCanonical
  have hcontinue' := hcontinue
  unfold composition_parts_continue at hcontinue'
  simp only [hA, hA1, hA2, hMask, hselectors, hsops, hposeidon, hsemanticActual, hI1, hclaim1,
    hcopyVariant, hcopy, hnew, hI2, hclaim2, bind_tc_ok] at hcontinue'
  simp [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_tc_ok] at hcontinue'
  rw [hloop0] at hcontinue'
  simp only [bind_tc_ok] at hcontinue'
  rw [hloop1] at hcontinue'
  simp only [bind_tc_ok] at hcontinue'
  have htuple : (out, a, maskOnly, g, h1Z, copy.active) =
      (composition, c1, mask, g, h1Z, copyActive) := by
    injection hcontinue' with houter
    injection houter with htuple
  have hout : out = composition := congrArg Prod.fst htuple
  rw [← hout]
  have hh1 : CanonicalQM h1Z :=
    selected_h1_success_canonical_current
      claims iH h1Z hclaims hI1 hclaim1
  exact ⟨houtCanonical, hh1⟩

#print axioms caller_success_composition_and_h1_canonical_currentTower
end AspisR1.TerminalV4CompositionCallerCanonicalV5
end
