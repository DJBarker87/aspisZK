import TerminalV4CompositionPartsContinueChunk07cV1
import TerminalV4CompositionLoopArrayPreparedCallV2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionLoop1SuccessExtractV1
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier

theorem loop1_success_of_continue_success
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (o : Option Std.U32) (claims : Array QM 84#usize)
    (point : Array QM 10#usize) (lambda chi theta : QM)
    (a a1 a2 : Array QM 16#usize) (maskOnly : Array QM 10#usize)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
    (poseidon : Aeneas.Std.Array QM 4#usize)
    (semantic : Aeneas.Std.Array QM 24#usize)
    (h1Z : QM) (pvpfcvv : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (iH iG : Std.Usize) (middle composition g : QM) (c1 : Array QM 16#usize)
    (mask : Array QM 10#usize) (copyActive : QM) (prepared : Prepared)
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
    (hsemantic : semanticEval { public1 with withdrawal_amount := o }
      { z := a, succ_z := a1, xor12_z := a2 } selectors = .ok semantic)
    (hI1 : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok iH)
    (hclaim1 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iH = .ok h1Z)
    (hcopyVariant : pool_v1.pair_forest_semantic_terminal.copy_variant public1.variant = .ok pvpfcvv)
    (hcopy : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1Z selectors lambda chi
      public1.transition.live_snapshot.next_pair_index pvpfcvv = .ok copy)
    (hnew : field.PreparedQm31Multiplier.new theta = .ok prepared)
    (hloop0 : pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
      ⟨semantic.val⟩ prepared copy.residual = .ok middle)
    (hI2 : pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN = .ok iG)
    (hclaim2 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iG = .ok g)
    (hcontinue : composition_parts_continue poseidonEval semanticEval public1 o claims point lambda chi theta =
      .ok (.Ok (composition, c1, mask, g, h1Z, copyActive))) :
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
      ⟨poseidon.val⟩ prepared middle = .ok composition := by
  have hc := hcontinue
  unfold composition_parts_continue at hc
  simp only [hA, hA1, hA2, hMask, hselectors, hsops, hposeidon, hsemantic, hI1, hclaim1,
    hcopyVariant, hcopy, hnew, hI2, hclaim2, bind_tc_ok] at hc
  simp [Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    core.iter.traits.iterator.Iterator.rev.default, bind_tc_ok] at hc
  rw [hloop0] at hc
  simp only [bind_tc_ok] at hc
  cases hloop1 : pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
      ⟨poseidon.val⟩ prepared middle with
  | ok out =>
    simp only [hloop1, bind_tc_ok] at hc
    have hout : out = composition := by
      injection hc with houter
      injection houter with htuple
      exact congrArg Prod.fst htuple
    simpa [hout] using hloop1
  | fail err => simp [hloop1] at hc
  | div => simp [hloop1] at hc

#print axioms loop1_success_of_continue_success
end AspisR1.TerminalV4CompositionLoop1SuccessExtractV1
end
