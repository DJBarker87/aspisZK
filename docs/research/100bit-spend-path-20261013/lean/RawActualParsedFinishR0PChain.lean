import RawActualParsedFinishWideEndpoint
import ActualMainMaskR0PValue

/-! Actual strict parsing, begin and finish imply a semantic-view chain whose
masked endpoint uses the existing R0P selected mask definition. Claims,
array-library and public-terminal implementation obligations remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualParsedFinishR0PChain
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun
open AspisR1PublicPreparation.RawActualParsedSemanticChain
open AspisR1PublicPreparation.RawActualParsedSemanticViewChain

 def r0pEndpoint (mask16 : Array RawSemanticFieldOwnerAdapter.MainQM 16#usize)
    (mask10 : Array RawSemanticFieldOwnerAdapter.MainQM 10#usize)
    (g : RawSemanticFieldOwnerAdapter.MainQM)
    (alpha : Array RawSemanticFieldOwnerAdapter.MainQM 10#usize)
    (eta terminal extra : RawSemanticFieldOwnerAdapter.MainQM) : W :=
    ActualMainMaskSemanticBridge.maskValue mask16 mask10 g alpha +
      algebraMap K W (fieldValue eta) * algebraMap K W (fieldValue terminal) +
        algebraMap K W (fieldValue extra)

 theorem parsed_finish_r0p_chain
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
      ∃ values : AspisR1.SemanticPrefixCodec.Full,
      ∃ initial : RawSemanticFieldOwnerAdapter.MainQM,
      ∃ entries : List (RoundEvidence D pre),
      RoundModel.rounds RawActualSemanticRoundCanonicality.actualRoundBoundaries
        D pre before = .ok (.Ok (running,out.alpha,afterRounds)) ∧
      AspisR1.SemanticPrefixCodec.encodeFull values = PrefixAdapter.completedRecords pre ∧
      AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize aspis_core.field.QM31.ZERO, before)
        (running,out.alpha,afterRounds) entries ∧
      entries.map RoundEvidence.q = out.alpha.val ∧
      B.terminal pub out.claims out.alpha challenges = .ok (.Ok terminal) ∧
      B.fromFn 16#usize (FinishModel.closureFn9 D) out.claims = .ok mask16 ∧
      B.fromFn 10#usize (FinishModel.closureFn5 D) out.claims = .ok mask10 ∧
      Array.index_usize out.claims 0#usize = .ok claim0 ∧
      Array.index_usize claim0 27#usize = .ok claim27 ∧
      Array.index_usize out.extra 28#usize = .ok extra28 ∧
      (CanonicalArray mask16 → CanonicalArray mask10 →
        Canonical (mainToProbe claim27) → Canonical (mainToProbe terminal) →
        RawGenericPolynomialSumcheckChain.Chain
          (AspisR1.SemanticPayloadView.claimAt14 values)
          (r0pEndpoint mask16 mask10 claim27 out.alpha challenges.eta terminal extra28)
          (viewPairs D pre values entries)) := by
  obtain ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
      values,initial,entries,hrounds,hfull,hrun,hqs,hterminal,
      hm16,hm10,hc0,hc27,hextra,hchain⟩ :=
    RawActualParsedFinishWideEndpoint.parsed_finish_wide_chain
      B D pub bytes pre hparse beforeBegin before challenges hbegin obs out hfinish
  have hpoint := (ActualFinishInputCanonicality.finish_alpha_and_tails_canonical
    (withConcreteArithmetic B) D pub pre before challenges obs out hfinish).1
  refine ⟨running,afterRounds,terminal,mask16,mask10,claim0,claim27,extra28,
    values,initial,entries,hrounds,hfull,hrun,hqs,hterminal,
    hm16,hm10,hc0,hc27,hextra, ?_⟩
  intro hm16c hm10c hgc hterminalc
  have h := hchain hm16c hm10c hgc hterminalc
  have hmask := ActualMainMaskR0PValue.mapped_populated_mask_eq_R0P
    mask16 mask10 claim27 out.alpha hm16c hm10c hgc hpoint
  unfold RawActualParsedFinishWideEndpoint.wideEndpoint at h
  rw [hmask] at h
  exact h

#print axioms parsed_finish_r0p_chain
end AspisR1PublicPreparation.RawActualParsedFinishR0PChain
end
