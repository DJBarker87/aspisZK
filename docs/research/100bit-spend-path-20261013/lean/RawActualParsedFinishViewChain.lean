import ActualFinishReachedFieldEquation
import RawActualParsedSemanticViewChain

/-! The strict parsed semantic view, actual sumcheck run and exact finish
field endpoint share the running value recovered from one successful finish.
This retains the explicit claim/terminal boundaries of the finish model. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedFinishViewChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

 theorem parsed_finish_view_chain
    (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (pre : r1_wire.Prefix)
    (hparse : PrefixAdapter.parseAccepted bytes = .ok (.Ok pre))
    (beforeBegin before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (hbegin : r1_wire.begin D pre beforeBegin = .ok (.Ok challenges,before))
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish RawActualSemanticRoundCanonicality.actualRoundBoundaries
      (withConcreteArithmetic B) D pub pre before challenges obs = .ok (.Ok out)) :
    ∃ running afterRounds terminal mask16 mask10 claim0 claim27 extra28,
      ∃ values : AspisR1.SemanticPrefixCodec.Full, ∃ initial : RawSemanticFieldOwnerAdapter.MainQM,
      ∃ entries : List (RoundEvidence D pre),
      RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries
        D pre before = .ok (.Ok (running,out.alpha,afterRounds)) ∧
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, before)
        (running,out.alpha,afterRounds) entries ∧
      entries.map RoundEvidence.q = out.alpha.val ∧
      RawGenericPolynomialSumcheckChain.Chain
        (AspisR1.SemanticPayloadView.claimAt14 values)
        (algebraMap K W (DecodeMain running))
        (viewPairs D pre values entries) ∧
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
    ActualFinishReachedFieldEquation.finish_success_reached_field_equation
      B D pub pre beforeBegin before challenges hbegin obs out hfinish
  obtain ⟨values,initial,entries,hfull,hrun,hqs,hchain⟩ :=
    parsed_rounds_semantic_view_chain bytes pre hparse D before afterRounds
      running out.alpha hrounds
  exact ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    values,initial,entries,hrounds,hfull,hrun,hqs,hchain,hterminal,
    hm16,hm10,hc0,hc27,hextra,heq⟩

#print axioms parsed_finish_view_chain
end AspisR1PublicPreparation.RawActualParsedFinishViewChain
end
