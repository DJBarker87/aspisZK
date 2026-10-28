import NDO_JFy_CompositionPrefix
import NDO_JFy_PoseidonPrefix
import NDO_JFy_SemanticPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CompositionTail
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal
def tail (selected : Array field.QM31 84#usize) (a a1 a2 : Array field.QM31 16#usize)
    (mask_only : Array field.QM31 10#usize)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
    (leading full internal : field.QM31) (path : Array field.QM31 24#usize) :
    Result (core.result.Result (field.QM31 × Array field.QM31 16#usize × Array field.QM31 10#usize ×
      field.QM31 × field.QM31 × field.QM31) PoolV1PairForestSemanticTerminalErrorV1) := do
  let public1 := JFu_PublicSemantic.value
  let o : Option U32 := none
  let point := JFu_TerminalPrefix.alpha
  let lambda := JFu_TerminalPrefix.challenges.lambda
  let chi := JFu_TerminalPrefix.challenges.chi
  let theta := JFu_TerminalPrefix.challenges.theta
  let poseidon ←
    JFy_PoseidonPrefix.tail
      { z := a, succ_z := a1, xor12_z := a2 } sops leading full internal
  let semantic ←
    JFy_SemanticPrefix.tail
      { public1 with withdrawal_amount := o }
      { z := a, succ_z := a1, xor12_z := a2 } selectors path
  let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  let h1_z ←
    pool_v1.pair_forest_semantic_terminal.selected_claim selected 0#usize i
  let pvpfcvv ←
    pool_v1.pair_forest_semantic_terminal.copy_variant public1.variant
  let copy ←
    pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1_z
      selectors lambda chi public1.transition.live_snapshot.next_pair_index
      pvpfcvv
  let prepared_theta ← field.PreparedQm31Multiplier.new theta
  let ii ←
    FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      semantic
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
      field.QM31 24#usize)
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 24#usize) ii
  let composition ←
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter
      prepared_theta copy.residual
  let ii1 ←
    FIq_Native.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
      poseidon
  let iter1 ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
      field.QM31 4#usize)
      (core.array.iter.IntoIter.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      field.QM31 4#usize) ii1
  let composition1 ←
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
      prepared_theta composition
  let i1 ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim selected 0#usize i1
  ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z,
    copy.active))

theorem source (selected : Array field.QM31 84#usize) (a b c : Array field.QM31 16#usize)
    (m : Array field.QM31 10#usize) (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (ps : state_only_poseidon.StateOnlyPoseidonSelectors) (leading full internal : field.QM31)
    (path : Array field.QM31 24#usize)
    (hpos : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ ps=
      JFy_PoseidonPrefix.tail ⟨a,b,c⟩ ps leading full internal)
    (hsem : semantic_packed JFu_PublicSemantic.value ⟨a,b,c⟩ s=
      JFy_SemanticPrefix.tail JFu_PublicSemantic.value ⟨a,b,c⟩ s path) :
    JFy_CompositionPrefix.tail selected a b c m s ps=tail selected a b c m s ps leading full internal path := by
  unfold JFy_CompositionPrefix.tail tail
  dsimp only
  erw [hpos,hsem]
  rfl
#print axioms source
end AspisR1.JFy_CompositionTail
end
