import ActualFinishFieldEquation

/-! Keep the final exact-field equation attached to the witnesses recovered
from the same successful finish. Canonicality of reached inputs is explicit;
no independent desired mask/arithmetic equation is a premise. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.ActualFinishFieldWitnesses
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge

 theorem finish_success_field_witnesses
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish R (withConcreteArithmetic B) D pub pre before
      challenges obs = .ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 extra28,
      RoundModel.rounds R D pre before = .ok (.Ok (running,out.alpha,afterRounds)) ∧
      B.terminal pub out.claims out.alpha challenges = .ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = .ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = .ok mask10 ∧
      Array.index_usize out.claims 0#usize = .ok claim0 ∧
      Array.index_usize claim0 27#usize = .ok claim27 ∧
      Array.index_usize out.extra 28#usize = .ok extra28 ∧
      (CanonicalArray mask16 → CanonicalArray mask10 →
        Canonical (mainToProbe claim27) → CanonicalArray out.alpha →
        Canonical (mainToProbe challenges.eta) → Canonical (mainToProbe terminal) →
        Canonical (mainToProbe extra28) →
        Canonical (mainToProbe running) ∧
          fieldValue running = maskValue mask16 mask10 claim27 out.alpha +
            fieldValue challenges.eta * fieldValue terminal + fieldValue extra28) := by
  obtain ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,mask,
      etaTerminal,masked,extra28,hrounds,hterminal,hm16,hm10,hc0,hc27,
      hmask,heta,hadd,hextra,hfinal⟩ :=
    finish_success_calls_concrete_arithmetic R B D pub pre before challenges obs out hfinish
  refine ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    hrounds, ?_, ?_, ?_,hc0,hc27,hextra, ?_⟩
  · simpa only [withConcreteArithmetic] using hterminal
  · simpa only [withConcreteArithmetic] using hm16
  · simpa only [withConcreteArithmetic] using hm10
  · intro hm16c hm10c hgc hpointc hetac hterminalc hextrac
    exact ActualFinishFieldEquation.terminal_chain_equation
      mask16 mask10 claim27 out.alpha challenges.eta terminal extra28 running
      mask etaTerminal masked hm16c hm10c hgc hpointc hetac hterminalc hextrac
      hmask heta hadd hfinal

#print axioms finish_success_field_witnesses
end AspisR1PublicPreparation.ActualFinishFieldWitnesses
end
