import CuSavingsRetainedCompositionGammaPreparation

/-! Complete actual old/new tx1 execution at candidate 1. All parse, semantic,
observer, allocation and finish failures/divergence are retained. The local
claim-factor source obligation remains explicit; preparations are the actual
previously checked bodies, not new uninterpreted parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace AspisR1.CuSavingsRetainedCompositionGammaTx1
open Aeneas Aeneas.Std Result AspisR1RhoPowerTail
open CuSavingsRetainedCompositionGammaTable CuSavingsRetainedCompositionGammaPreparation

private theorem bind_ext {A B : Type} (m : Result A) (f g : A → Result B)
    (h : ∀ x, f x = g x) : (do let x ← m; f x) = (do let x ← m; g x) := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok x => exact h x

variable [PreparedCommon] [AspisR1CuRho.ScalarKBlocks] [AspisR1CuRho.HeapReserve] [RetainedPrefix]

theorem source_eq_of_claim_factor (finish : Finish) {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (claim_factor : ∀ (sem : r1_semantic.Verified H) (v : verifier.View) gamma kappa,
      retained.oldClaim D sem v.y1 v.inactive gamma kappa =
        (do let g ← weights.powers 29#usize gamma
            gamma_new.prepared_claim D sem v.y1 v.inactive g kappa)) :
    retained.old_tx1 finish D publicValue publicBytes proof k hash obs =
      retained.tx1 finish D publicValue publicBytes proof k hash obs := by
  unfold retained.old_tx1 retained.tx1
  split
  · rfl
  · apply bind_ext
    intro parsed
    cases parsed with
    | Err error => rfl
    | Ok v =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply bind_ext
      intro marked
      cases marked
      unfold retained.old_tx1_prepare retained.tx1_prepare
      simp only [bind_assoc_eq]
      apply bind_ext
      intro semanticResult
      cases semanticResult with
      | Err error => rfl
      | Ok sem =>
        simp only [core.result.Result.map_err,AspisR1PublicPreparation.core.result.Result.map_err,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch,bind_assoc_eq]
        apply bind_ext
        intro semanticMarked
        cases semanticMarked
        let initial := Array.repeat 29#usize aspis_core.field.WideExact.ZERO
        rw [preparations_eq D sem v hash initial (claim_factor sem v)]
        simp only [erase,bind_assoc_eq]
        cases hprep : gamma_new.Prepared.gamma_new_new D sem v hash initial with
        | fail error => rfl
        | div => rfl
        | ok pair =>
          rcases pair with ⟨result,g⟩
          cases result with
          | Err error => rfl
          | Ok p =>
            have hpow := CuSavingsRetainedCompositionGammaTable.source_success D sem v hash initial p g hprep
            simp only [bind_tc_ok,uncurry_apply_pair,
              core.result.Result.Insts.CoreOpsTry.branch]
            rw [hpow]
            simp only [bind_tc_ok]
            rfl

#print axioms source_eq_of_claim_factor
end AspisR1.CuSavingsRetainedCompositionGammaTx1
