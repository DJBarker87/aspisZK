import TerminalV4CompositionLoopArrayPreparedCallV2
import TerminalV4PreparedMulCanonicalV1
import TerminalV4RevListTransitionV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AspisR1.TerminalV4CompositionPartsTwoFoldCanonical
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM
abbrev PreparedFor := AspisR1.TerminalV4PreparedStateCurrent.PreparedFor

private theorem bindPairOk {A B C : Type} (a : A) (b : B)
    (f : A → B → Result C) :
    (do let (x, y) ← Result.ok (a, b); f x y) = f a b := rfl

theorem composition_parts_loop1_canonical
    (items : List QM) (prepared : Prepared) (linear acc : QM)
    (hlinear : CanonicalQM linear)
    (hprepared : PreparedFor prepared linear)
    (hacc : CanonicalQM acc)
    (hitems : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel linear items) :
    ∃ out : QM,
      AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
        ⟨items.reverse⟩ prepared acc = .ok out ∧ CanonicalQM out := by
  induction items generalizing acc with
  | nil =>
      rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1.eq_def]
      simp only [Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator,
        core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back,
        List.reverse_nil, bind_tc_ok]
      exact ⟨acc, rfl, hacc⟩
  | cons x xs ih =>
      have hx : CanonicalQM x := hitems x (by simp)
      have htail : AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel linear xs := by
        intro y hy
        exact hitems y (by simp [hy])
      obtain ⟨q, hq, hqcan⟩ :=
        AspisR1.TerminalV4PreparedMulCanonical.prepared_mul_canonical
          prepared linear acc hlinear hacc hprepared
      classical
      let acc1 : QM := Classical.choose
        (AspisR1.TerminalV4TowerAdd.current_qm_add_mod q x hqcan hx)
      have haddPack := Classical.choose_spec
        (AspisR1.TerminalV4TowerAdd.current_qm_add_mod q x hqcan hx)
      have hadd := haddPack.1
      have hacc1 := haddPack.2.1
      have hcall :
          AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
            ⟨(x :: xs).reverse⟩ prepared acc =
          AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
            ⟨xs.reverse⟩ prepared acc1 := by
        rw [List.reverse_cons]
        rw [AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1.eq_def]
        rw [AspisR1.TerminalV4RevListTransitionV2.reverse_next_append]
        rw [bindPairOk]
        rw [hq]
        simp only [bind_tc_ok]
        rw [hadd]
        simp only [bind_tc_ok]
        rfl
      obtain ⟨out, hrun, hout⟩ := ih acc1 hacc1 htail
      exact ⟨out, hcall.trans hrun, hout⟩

theorem listLoopCanonicalModel_of_four_array
    (items : Aeneas.Std.Array QM 4#usize) (linear : QM)
    (hcanonical : ∀ i : Fin 4,
      CanonicalQM (items.val[i.val]'(by simpa [items.property] using i.isLt))) :
    AspisR1.TerminalV4CompositionLoopCanonical.listLoopCanonicalModel
      linear items.val.reverse := by
  intro x hx
  have hx' : x ∈ items.val := List.mem_reverse.mp hx
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hx'
  have hi4 : i < 4 := by simpa [items.property] using hi
  have hci := hcanonical ⟨i, hi4⟩
  simpa [hget] using hci

/-- Canonicality for the two actual reverse folds used by composition_parts.
The generated prepared constructor is invoked by the proof; only canonicality
of the actual operands and pointwise canonicality of the two input arrays are
caller premises. -/
theorem composition_parts_two_folds_after_prepared_new
    (semantic : Aeneas.Std.Array QM 24#usize)
    (poseidon : Aeneas.Std.Array QM 4#usize) (theta seed : QM)
    (htheta : CanonicalQM theta) (hseed : CanonicalQM seed)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt)))
    (hposeidonCanonical : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt))) :
    ∃ prepared : Prepared, field.PreparedQm31Multiplier.new theta = .ok prepared ∧
      ∃ middle : QM,
        AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
          ⟨semantic.val⟩ prepared seed = .ok middle ∧ CanonicalQM middle ∧
        ∃ out : QM,
          AspisR1SelectedMaskProbe.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
            ⟨poseidon.val⟩ prepared middle = .ok out ∧ CanonicalQM out := by
  obtain ⟨prepared, hnew, hprepared⟩ :=
    AspisR1.TerminalV4PreparedStateCurrent.current_prepared_new theta htheta
  obtain ⟨middle, hloop0, hmiddleCan, _hpoly⟩ :=
    AspisR1.TerminalV4CompositionLoopArrayPolynomialCaller.composition_parts_loop0_array_polynomial_of_pointwise_canonical
      semantic prepared theta seed htheta hprepared hseed hsemanticCanonical
  have hposeidonItems := listLoopCanonicalModel_of_four_array poseidon theta hposeidonCanonical
  obtain ⟨out, hloop1, houtCan⟩ :=
    composition_parts_loop1_canonical poseidon.val.reverse prepared theta middle
      htheta hprepared hmiddleCan hposeidonItems
  refine ⟨prepared, hnew, middle, hloop0, hmiddleCan, out, ?_, houtCan⟩
  simpa only [List.reverse_reverse] using hloop1

#print axioms composition_parts_loop1_canonical
#print axioms listLoopCanonicalModel_of_four_array
#print axioms composition_parts_two_folds_after_prepared_new
end AspisR1.TerminalV4CompositionPartsTwoFoldCanonical
