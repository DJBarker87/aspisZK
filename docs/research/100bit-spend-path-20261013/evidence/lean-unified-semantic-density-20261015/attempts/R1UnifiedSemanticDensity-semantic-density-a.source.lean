import R1UnifiedSamplerLaw
import R1SemanticBudget

/-! Reuse the existing semantic event densities at the actual 0--24 indices.
The prefix decoder is an explicit function of the pre-challenge context.
No recovered-word, source-parser, or acceptance implication is asserted. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticDensity

open FS FS2 FS2.Duplex
open R0P R0P.SemSource R0P.Mask R0P.SemD3Glue
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open TranscriptView

variable {M : Type} {L : Nat} {Sfield : Fin 29 → Subfield SemE}
  {F : Subfield SemE}

abbrev DecodedSemantic (Sfield : Fin 29 → Subfield SemE) :=
  R0C.SemStatement.Prefix SemE SemE (TypedContext SemE Sfield) (SemMsgZ SemE) ×
    SemMsgZ SemE

def semanticBad (B : PackBasis F)
    (decoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (DecodedSemantic Sfield))
    (P : UnifiedSampler.Prefix M SemE L) (m : Message M)
    (T : Table (Addr L) State) (ch : Challenge SemE) : Prop :=
  if P.rounds.length < 25 ∧ UnifiedSampler.messageValid P.rounds.length m then
    match decoded P m T, ch.1 with
    | some (sp, sm), .ordinary value =>
        sp.rounds.length = P.rounds.length ∧
          semanticBadZ (maskClaimsR0 B) B sp sm value
    | _, _ => False
  else False

def rowBudget (i : Nat) : ℚ := if i < 25 then combinedD2BudgetZ i else 0

private theorem budget_nonneg (i : Nat) : 0 ≤ rowBudget i := by
  unfold rowBudget
  split_ifs with hi
  · rw [SemanticBudget.budget_eq ⟨i, hi⟩]
    unfold SemanticBudget.atom
    have := R0P.SemSource.deltaQ_nonneg
    positivity
  · exact le_rfl

theorem semantic_density_bound (p : Params M SemE L) (hD : 5 ≤ p.D)
    (B : PackBasis F)
    (decoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (DecodedSemantic Sfield))
    (hsigma : ∀ i, i < 25 → ∀ s : State, p.σ i s = semChal s)
    (T : Table (Addr L) State) (i : Nat)
    (P : UnifiedSampler.Prefix M SemE L) (m : Message M)
    (hround : P.rounds.length = i) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (semanticBad B decoded P m T w.2)) ≤ rowBudget i := by
  by_cases hvalid : P.rounds.length < 25 ∧ UnifiedSampler.messageValid P.rounds.length m
  · have hi : i < 25 := by omega
    have hm : UnifiedSampler.messageValid i m := by simpa [hround] using hvalid.2
    rw [UnifiedSampler.unified_law p hD i P m
      (fun ch => indicator (semanticBad B decoded P m T ch)) (by omega) hm]
    cases hd : decoded P m T with
    | none =>
        simpa [semanticBad, hvalid, hd, mean_const] using budget_nonneg i
    | some data =>
        rcases data with ⟨sp, sm⟩
        by_cases hlen : sp.rounds.length = P.rounds.length
        · have hslen : sp.rounds.length < 25 := by omega
          have hb := semantic_round_densityZ (maskClaimsR0 B) B sp sm hslen
          simpa [semanticBad, hvalid, hd, hlen, TranscriptView.liftChallenge,
            hsigma i hi, mean_const, rowBudget, hi, hround] using hb
        · simpa [semanticBad, hvalid, hd, hlen, TranscriptView.liftChallenge,
            mean_const] using budget_nonneg i
  · have hz : (fun w : View (Addr L) State (Challenge SemE) =>
        indicator (semanticBad B decoded P m T w.2)) = fun _ => (0 : ℚ) := by
      funext w
      simp [semanticBad, hvalid]
    rw [hz, independentMean_const]
    exact budget_nonneg i

#print axioms semantic_density_bound
end AspisR1.UnifiedSemanticDensity
end
