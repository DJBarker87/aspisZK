import CompositionPartsTailSource

/-! The exact post-copy caller tail executes both retained Horner folds and
returns the selected q cell. The old polynomial theorem supplies the folds;
this adapter checks the actual source slice/reverse constructors and final read. -/
set_option autoImplicit false
namespace AspisR1.CompositionPartsTail
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.TerminalCompositionLoopAdapter
open scoped BigOperators
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

private theorem array_slice_len {α : Type} {n : Usize} (xs : Array α n) :
    Slice.len (Array.to_slice xs) = n := by
  apply UScalar.eq_of_val_eq
  simpa [Slice.len, Slice.length, Array.to_slice] using xs.property

/-- Source tail result from the actual coefficient arrays. No multiplier,
loop success or selected-cell success is assumed. The semantic/Poseidon
coefficient equations are source/model obligations of the enclosing caller. -/
theorem tail_success
    (semantic : Array QM 24#usize) (poseidon : Array QM 4#usize)
    (theta seed active : QM) (claims : Array QM 84#usize)
    (a : Array QM 16#usize) (mask_only : Array QM 10#usize) (h1_z : QM)
    (lanes : Fin 29 → ExactQM)
    (htheta : CanonicalQM theta) (hseed : CanonicalQM seed)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt)))
    (hposeidonCanonical : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)))
    (hclaims : ∀ i : Fin 84,
      CanonicalQM (claims.val[i.val]'(by simpa [claims.property] using i.isLt)))
    (hsemantic : ∀ i : Fin 24,
      coefficient24 semantic i.val = lanes (Fin.natAdd 4 (Fin.castAdd 1 i)))
    (hposeidon : ∀ i : Fin 4,
      coefficient4 poseidon i.val = lanes (Fin.castAdd 25 i))
    (hcopy : decode seed = lanes 28) :
    ∃ out q,
      run semantic poseidon theta seed active claims a mask_only h1_z =
        .ok (core.result.Result.Ok (out, a, mask_only, q, h1_z, active)) ∧
      CanonicalQM out ∧ CanonicalQM q ∧
      q = claims.val[27]'(by simpa [claims.property] using (show 27 < 84 by omega)) ∧
      decode out = ∑ i : Fin 29, decode theta ^ i.val * lanes i := by
  obtain ⟨prepared, middle, out, hnew, hfirst, hsecond, hcanonical, hvalue⟩ :=
    AspisR1.TerminalCompositionPolynomial.prepared_folds_eq_lane_sum
      semantic poseidon theta seed lanes htheta hseed hsemanticCanonical
      hposeidonCanonical hsemantic hposeidon hcopy
  obtain ⟨q, hq, hqvalue, hqcanonical⟩ := selected_claim_success claims 0#usize 27#usize
    (by norm_num) (by norm_num) hclaims
  refine ⟨out, q, ?_, hcanonical, hqcanonical, ?_, hvalue⟩
  · simp only [run, hnew, bind_tc_ok, lift, array_slice_len,
      core.iter.traits.iterator.Iterator.rev.trait_default,
      core.iter.traits.iterator.Iterator.rev.default]
    change (do
      let composition ← pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
        (AspisR1.TerminalCompositionPolynomial.reverseRange 24#usize) semantic prepared seed
      let composition1 ← pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        (AspisR1.TerminalCompositionPolynomial.reverseRange 4#usize) poseidon prepared composition
      let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
      let q ← pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i
      ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z, active))) = _
    rw [hfirst]
    simp only [bind_tc_ok, hsecond, selected_g_column_ok, hq]
  · simpa using hqvalue

#print axioms tail_success
end AspisR1.CompositionPartsTail
