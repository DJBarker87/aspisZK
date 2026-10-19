import ActualFinishInputCanonicality
import ActualBeginSelectedCanonical

/-! The exact finish equation with canonical alpha, extra and eta derived
from the actual successful begin/round/decode execution. Claim-producing and
public-terminal boundaries remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualFinishReachedFieldEquation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge

 theorem begin_eta_canonical {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre before = .ok (.Ok challenges,after)) :
    Canonical (mainToProbe challenges.eta) := by
  have h := ActualBeginSelectedCanonical.begin_challenges_selected_canonical
    D pre before after challenges hbegin
  simpa only [ActualBeginSelectedCanonical.ToSelected,
    SemanticCallSelectedCanonical.toSelected, mainToProbe] using h.2.2.2.2.1

 theorem finish_success_reached_field_equation
    (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (beforeBegin before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre beforeBegin = .ok (.Ok challenges,before))
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish RawActualSemanticRoundCanonicality.actualRoundBoundaries
      (withConcreteArithmetic B) D pub pre before challenges obs = .ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 extra28,
      RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries
        D pre before = .ok (.Ok (running,out.alpha,afterRounds)) ∧
      B.terminal pub out.claims out.alpha challenges = .ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = .ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = .ok mask10 ∧
      Array.index_usize out.claims 0#usize = .ok claim0 ∧
      Array.index_usize claim0 27#usize = .ok claim27 ∧
      Array.index_usize out.extra 28#usize = .ok extra28 ∧
      (CanonicalArray mask16 → CanonicalArray mask10 →
        Canonical (mainToProbe claim27) → Canonical (mainToProbe terminal) →
        Canonical (mainToProbe running) ∧
          fieldValue running = maskValue mask16 mask10 claim27 out.alpha +
            fieldValue challenges.eta * fieldValue terminal + fieldValue extra28) := by
  obtain ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
      hrounds,hterminal,hm16,hm10,hc0,hc27,hextra,heq⟩ :=
    ActualFinishFieldWitnesses.finish_success_field_witnesses
      RawActualSemanticRoundCanonicality.actualRoundBoundaries B D pub pre before
      challenges obs out hfinish
  have hc := ActualFinishInputCanonicality.finish_alpha_and_tails_canonical
    (withConcreteArithmetic B) D pub pre before challenges obs out hfinish
  have hetac := begin_eta_canonical D pre beforeBegin before challenges hbegin
  have hextrac := ActualFinishInputCanonicality.canonical_index_of_success
    out.extra hc.2.1 28#usize (by decide) extra28 hextra
  refine ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    hrounds,hterminal,hm16,hm10,hc0,hc27,hextra, ?_⟩
  intro hm16c hm10c hgc hterminalc
  exact heq hm16c hm10c hgc hc.1 hetac hterminalc hextrac

#print axioms begin_eta_canonical
#print axioms finish_success_reached_field_equation
end AspisR1PublicPreparation.ActualFinishReachedFieldEquation
end
