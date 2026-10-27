import RPt_FIq_S_RawActualAnnotatedPolynomialRun

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualAnnotatedChallengeSequence

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun

abbrev MainQM := AspisR1PublicPreparation.RawGeneratedSemanticRoundPolynomialAdapter.MainQM

/-- The q values recorded in annotated entries themselves form the extracted
SemanticRun for the same rows and transcript states. -/
theorem annotatedRun_semantic {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (events : List (Usize × U8)) (initial final : Outcome H)
    (entries : List (RoundEvidence D pre))
    (hrun : AnnotatedRun D pre events initial final entries) :
    AspisR1PublicPreparation.BeginCalls.SemanticRun D pre (events.map Prod.snd)
      initial.2.2 final.2.2 (entries.map RoundEvidence.q) := by
  induction hrun with
  | nil out => exact .nil _
  | @cons entry events final entries tail ih =>
      simpa only [List.map_cons] using
        (AspisR1PublicPreparation.BeginCalls.SemanticRun.cons
          entry.recordOk entry.semanticOk ih)

/-- Successful semantic-call traces with the same start and row sequence have
the same ordered q values. The proof follows deterministic validated-record
and semantic calls, rather than assuming equality of arbitrary challenge lists. -/
theorem semanticRun_qs_unique {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    {rows : List U8} {self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H}
    {qs₁ qs₂ : List MainQM}
    (h₁ : AspisR1PublicPreparation.BeginCalls.SemanticRun D pre rows self after qs₁)
    (h₂ : AspisR1PublicPreparation.BeginCalls.SemanticRun D pre rows self after qs₂) :
    qs₁ = qs₂ := by
  induction h₁ generalizing qs₂ with
  | nil self =>
      cases h₂
      rfl
  | @cons row rows self mid₁ after q₁ qs₁ record₁ hrecord₁ hsemantic₁ tail₁ ih =>
      cases h₂ with
      | @cons _ _ _ mid₂ _ q₂ qs₂ record₂ hrecord₂ hsemantic₂ tail₂ =>
          have hrecord : record₁ = record₂ := by
            have hinner :
              (core.result.Result.Ok record₁ : core.result.Result
                AspisR1PublicPreparation.r1_wire.ValidatedRecord
                AspisR1PublicPreparation.r1_wire.Error) =
              core.result.Result.Ok record₂ := by
              injection (hrecord₁.symm.trans hrecord₂) with hinner
            cases hinner
            rfl
          subst record₂
          have hparts :
              ((core.result.Result.Ok q₁ : core.result.Result MainQM
                AspisR1PublicPreparation.r1_wire.Error), mid₁) =
              (core.result.Result.Ok q₂, mid₂) := by
            injection (hsemantic₁.symm.trans hsemantic₂) with hparts
          have hsemantic : q₁ = q₂ ∧ mid₁ = mid₂ := by
            have hp := Prod.mk.inj hparts
            have hq :
                (core.result.Result.Ok q₁ : core.result.Result MainQM
                  AspisR1PublicPreparation.r1_wire.Error) =
                core.result.Result.Ok q₂ := hp.1
            cases hq
            cases hp.2
            exact ⟨rfl, rfl⟩
          rcases hsemantic with ⟨hq, hmid⟩
          subst mid₂
          simp [hq, ih tail₂]

/-- Every challenge stored in the actual annotated ten-round source trace is
exactly the corresponding output of the successful rounds call. -/
theorem rounds_success_annotated_challenges_eq_alpha {H : Type}
    (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (self afterRounds : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (running : MainQM)
    (alpha : Array MainQM 10#usize)
    (hrounds : AspisR1PublicPreparation.RoundModel.rounds
      AspisR1PublicPreparation.RawActualSemanticRoundCanonicality.actualRoundBoundaries
      D pre self = .ok (.Ok (running, alpha, afterRounds))) :
    ∃ record decoded initial entries,
      AspisR1PublicPreparation.r1_wire.Prefix.validated_record pre 14#u8 =
        .ok (.Ok record) ∧
      AspisR1PublicPreparation.RawActualDecodeKMainAdapter.decodeMain
        1#usize record 0#usize = .ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize = .ok initial ∧
      AnnotatedRun D pre AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule
        (initial, Array.repeat 10#usize AspisR1PublicPreparation.aspis_core.field.QM31.ZERO, self)
        (running, alpha, afterRounds) entries ∧
      entries.map (fun entry => entry.q) = alpha.val := by
  obtain ⟨record, decoded, initial, qs, entries, hrecord, hdecode, hinitial,
      hsemanticRun, hqs, hannotated, hchain⟩ :=
    AspisR1PublicPreparation.RawActualAnnotatedPolynomialRun.rounds_success_actual_annotated
      D pre self afterRounds running alpha hrounds
  have hfromEntries := annotatedRun_semantic D pre _ _ _ entries hannotated
  have hrows : AspisR1PublicPreparation.SemanticRoundsCheckedTrace.schedule.map Prod.snd =
      AspisR1PublicPreparation.RoundCalls.rows := rfl
  have hentryRun : AspisR1PublicPreparation.BeginCalls.SemanticRun D pre
      AspisR1PublicPreparation.RoundCalls.rows self afterRounds
      (entries.map RoundEvidence.q) := by
    simpa only [hrows] using hfromEntries
  have hqsEq := semanticRun_qs_unique D pre hentryRun hsemanticRun
  exact ⟨record, decoded, initial, entries, hrecord, hdecode, hinitial,
    hannotated, hqsEq.trans hqs⟩

#print axioms annotatedRun_semantic
#print axioms semanticRun_qs_unique
#print axioms rounds_success_annotated_challenges_eq_alpha
end AspisR1PublicPreparation.RawActualAnnotatedChallengeSequence
end
