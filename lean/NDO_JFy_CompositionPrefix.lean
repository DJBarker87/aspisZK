import NDO_JFy_CompositionGathers
import NDO_JFy_RealSelectors
import NDO_JFu_TerminalPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_CompositionPrefix
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal

def tail (selected : Array field.QM31 84#usize) (a a1 a2 : Array field.QM31 16#usize)
    (mask_only : Array field.QM31 10#usize)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (sops : state_only_poseidon.StateOnlyPoseidonSelectors) :
    Result (core.result.Result (field.QM31 × Array field.QM31 16#usize × Array field.QM31 10#usize ×
      field.QM31 × field.QM31 × field.QM31) PoolV1PairForestSemanticTerminalErrorV1) := do
  let public1 := JFu_PublicSemantic.value
  let o : Option U32 := none
  let point := JFu_TerminalPrefix.alpha
  let lambda := JFu_TerminalPrefix.challenges.lambda
  let chi := JFu_TerminalPrefix.challenges.chi
  let theta := JFu_TerminalPrefix.challenges.theta
  let poseidon ←
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
      { z := a, succ_z := a1, xor12_z := a2 } sops
  let semantic ←
    pool_v1.pair_forest_semantic_terminal.semantic_packed
      { public1 with withdrawal_amount := o }
      { z := a, succ_z := a1, xor12_z := a2 } selectors
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

theorem source (selected : Array field.QM31 84#usize) (hc : FIw_ArrayValue.canonical selected) :
    ∃ a b c m selectors sops,
    composition_parts JFu_PublicSemantic.value selected JFu_TerminalPrefix.alpha
      JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi JFu_TerminalPrefix.challenges.theta=
      tail selected a b c m selectors sops ∧
    FIw_ArrayValue.canonical a ∧ FIw_ArrayValue.canonical b ∧ FIw_ArrayValue.canonical c ∧ FIw_ArrayValue.canonical m ∧
    pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha=ok selectors ∧
    FIw_ArrayValue.canonical selectors.high ∧ FIw_ArrayValue.canonical selectors.low ∧
    poseidon_selectors selectors=ok sops ∧ FIv_NativeValue.Canon sops.block ∧ FIw_ArrayValue.canonical sops.«local» := by
  obtain ⟨a,b,c,m,⟨ha,hac⟩,⟨hb,hbc⟩,⟨hcc,hccc⟩,⟨hm,hmc⟩⟩ := JFy_CompositionGathers.source selected hc
  obtain ⟨selectors,sops,hs,hsh,hsl,hps,hpb,hpl⟩ := JFy_RealSelectors.source
  refine ⟨a,b,c,m,selectors,sops,?_,hac,hbc,hccc,hmc,hs,hsh,hsl,hps,hpb,hpl⟩
  unfold composition_parts
  have noneAmount : JFu_PublicSemantic.value.withdrawal_amount=none := rfl
  rw [noneAmount,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,Bool.false_eq_true,ite_false]
  have updated : {JFu_PublicSemantic.value with withdrawal_amount:=none}=JFu_PublicSemantic.value := rfl
  try rw [updated]
  rw [JFu_Transition.source,bind_tc_ok]
  simp only [Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rw [ha,bind_tc_ok,hb,bind_tc_ok,hcc,bind_tc_ok,hm,bind_tc_ok,hs,bind_tc_ok,hps,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFy_CompositionPrefix
end
