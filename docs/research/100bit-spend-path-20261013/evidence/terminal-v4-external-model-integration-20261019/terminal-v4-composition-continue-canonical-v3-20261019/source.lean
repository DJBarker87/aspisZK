import TerminalV4CompositionPartsTwoFoldCanonicalV1
import TerminalV4CompositionPartsContinueChunk07cV1

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AspisR1.TerminalV4CompositionContinueCanonical
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.TerminalV4TowerAdd.CanonicalQM

/-- A successful execution of the generated continuation returns a canonical
composition result, provided the two actual evaluator callbacks return arrays
whose entries are canonical and the selected-copy residual is canonical. The
success assumptions are exact calls made by the continuation; no totality or
canonicality of either evaluator is asserted. -/
theorem actual_continue_success_composition_canonical
    (poseidonEval : PoseidonEvaluator) (semanticEval : SemanticEvaluator)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (o : Option Std.U32) (claims : Array QM 84#usize)
    (point : Array QM 10#usize) (lambda chi theta : QM)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
    (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
    (poseidon : Aeneas.Std.Array QM 4#usize)
    (semantic : Aeneas.Std.Array QM 24#usize)
    (a a1 a2 : Array QM 16#usize) (h1Z : QM)
    (pvpfcvv : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
    (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
    (iH iG : Std.Usize)
    (composition : QM) (c1 : Array QM 16#usize) (mask : Array QM 10#usize)
    (g : QM) (copyActive : QM)
    (htheta : CanonicalQM theta) (hseed : CanonicalQM copy.residual)
    (hsemanticCanonical : ∀ i : Fin 24,
      CanonicalQM (semantic.val[i.val]'(by simpa [semantic.property] using i.isLt)))
    (hposeidonCanonical : ∀ i : Fin 4,
      CanonicalQM (poseidon.val[i.val]'(by simpa [poseidon.property] using i.isLt)))
    (hselectors : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hsops : pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors = .ok sops)
    (hposeidon : poseidonEval { z := a, succ_z := a1, xor12_z := a2 } sops = .ok poseidon)
    (hsemantic : semanticEval { public1 with withdrawal_amount := o }
      { z := a, succ_z := a1, xor12_z := a2 } selectors = .ok semantic)
    (hI1 : pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN = .ok iH)
    (hclaim1 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iH = .ok h1Z)
    (hcopyVariant : pool_v1.pair_forest_semantic_terminal.copy_variant public1.variant = .ok pvpfcvv)
    (hcopy : pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h1Z
      selectors lambda chi public1.transition.live_snapshot.next_pair_index pvpfcvv = .ok copy)
    (hI2 : pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN = .ok iG)
    (hclaim2 : pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize iG = .ok g)
    (hcontinue : composition_parts_continue poseidonEval semanticEval public1 o claims point lambda chi theta =
      .ok (core.result.Result.Ok (composition, a, mask, g, h1Z, copyActive))) :
    CanonicalQM composition := by
  obtain ⟨prepared, hnew, middle, hloop0, hmiddleCanonical, out, hloop1, houtCanonical⟩ :=
    AspisR1.TerminalV4CompositionPartsTwoFoldCanonical.composition_parts_two_folds_after_prepared_new
      semantic poseidon theta copy.residual htheta hseed hsemanticCanonical hposeidonCanonical
  have hcomposition : composition = out := by
    unfold composition_parts_continue at hcontinue
    simp only [hselectors, hsops, hposeidon, hsemantic, hI1, hclaim1,
      hcopyVariant, hcopy, hnew, hloop0, hloop1, hI2, hclaim2] at hcontinue
    have ht := Result.ok.inj hcontinue
    cases ht
    rfl
  rw [hcomposition]
  exact houtCanonical

#print axioms actual_continue_success_composition_canonical
end AspisR1.TerminalV4CompositionContinueCanonical
end
