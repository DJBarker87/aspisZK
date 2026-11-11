import AspisRowDensityQM31
import R1LiteralRhoDensity

/-! Aspis per-step accounting, row densities: lift to the transcript samplers.

Kind of result: theorems in R1's sampler setting, one level up from
`AspisRowDensityQM31`: the independent-answer mean over the sampler program of
one row, which is the form the classifier's `density` field takes
(`LiteralClassifier.density`).

* `unified_row_density`: any `R1` unified-sampler instance (`UnifiedSampler.samp`
  for arbitrary parameters `p`), any row `i ≠ 31` with a valid message, whose
  challenge map has K-part `qm31Sample` on that row. The bad set `T` is a
  parameter, fixed together with the prefix `P` and this row's message `m`
  before the sampler runs. R1's `UnifiedSampler.unified_law` turns the mean
  over the sampler into a mean over one fresh block `p.σ i b`; `T` does not
  depend on `b`. `UnifiedSampler.samp` is defined for every row index (rows
  other than 0, 26 and 31 are `DuplexSamplers.plain`), so this covers rows 33
  to 39 of a 40-row instance that reuses `UnifiedSampler.samp`; R1's own
  `LiteralTranscript.valid` admits payload rows only below 33, so R1's literal
  transcript has no rows 33 to 39.
* `unified_read_density` and the three instances `combining_unified_density`,
  `round_unified_density`, `pair_unified_density`: the same with the bad set
  given by a read of `(P, m)` and an abstract set family with a cardinality
  hypothesis.
* `pair_row32_density`: R1's `LiteralRhoDensity.row32_density`, with R1's read
  and `rhoBad` replaced by an abstract read of the literal prefix and an
  abstract set family of size at most 21, cap `capPair`.
* `rho_mean_recovered`, `row32_density_recovered`: R1's `rho_mean` and
  `row32_density`, same statements, re-derived from the abstract forms. -/

set_option autoImplicit false
noncomputable section

namespace AspisRowDensity.Sampler

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.SourceDuplexStep
open AspisR1 AspisRowDensity.QM31
attribute [local instance] Classical.propDecidable

/-- The event of an ordinary row, as in `LiteralOrdinaryDensity.event` but
without the literal message schedule: the challenge is an ordinary value in
the bad predicate; a query value is never bad here. -/
def ordEvent (bad : E → Prop) (ch : TranscriptView.Challenge E) : Prop :=
  match ch.1 with
  | .ordinary v => bad v
  | .queries _ => False

/-- R1's selected challenge map has K-part `qm31Sample` on every row `i ≥ 32`. -/
theorem selected_sigma_rho (i : Nat) (hi : 32 ≤ i) (s : State) :
    SelectedChallengeMap.rhoOf (SelectedTranscriptParams.params.σ i s) =
      R0P.SemSource.qm31Sample s :=
  sigma_rho_of_ge i hi s

/-- Row density over any unified-sampler instance, for a bad set `T` of the
K-part with `|T| ≤ k`. -/
theorem unified_row_density {M : Type} {L : Nat}
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
    (P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
    (hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s)
    (T : Finset K) (k : Nat) (hT : T.card ≤ k) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (ordEvent (fun v => SelectedChallengeMap.rhoOf v ∈ T) w.2)) ≤
      (k : ℚ) * perElem := by
  rw [UnifiedSampler.unified_law p hD i P m
    (fun ch => indicator (ordEvent (fun v => SelectedChallengeMap.rhoOf v ∈ T) ch)) hi31 hm]
  simp only [ordEvent, TranscriptView.liftChallenge, mean_const, hσ]
  exact qm31_set_mass_le T k hT

/-- The same with the bad set read from the prefix and this row's message. -/
theorem unified_read_density {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (k : Nat) (hS : ∀ x, (S x).card ≤ k)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
    (P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
    (hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (ordEvent (setBad read S (P, m)) w.2)) ≤
      (k : ℚ) * perElem := by
  have he : setBad read S (P, m) =
      (fun v => SelectedChallengeMap.rhoOf v ∈ setOf read S (P, m)) :=
    funext (fun v => propext (setBad_iff read S (P, m) v))
  rw [he]
  exact unified_row_density p hD i P m hi31 hm hσ _ k (setOf_card read S k hS (P, m))

theorem combining_unified_density {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 1)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
    (P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
    (hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (ordEvent (setBad read S (P, m)) w.2)) ≤ capLambda := by
  have h := unified_read_density read S 1 hS p hD i P m hi31 hm hσ
  simpa only [capLambda, Nat.cast_one] using h

theorem round_unified_density {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 2)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
    (P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
    (hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (ordEvent (setBad read S (P, m)) w.2)) ≤ capRound := by
  have h := unified_read_density read S 2 hS p hD i P m hi31 hm hσ
  simpa only [capRound, Nat.cast_ofNat] using h

theorem pair_unified_density {M : Type} {L : Nat} {X : Type}
    (read : UnifiedSampler.Prefix M E L × TranscriptView.Message M → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 21)
    (p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
    (P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
    (hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
    (hσ : ∀ s, SelectedChallengeMap.rhoOf (p.σ i s) = R0P.SemSource.qm31Sample s) :
    independentMean (UnifiedSampler.samp p hD i P m).toProgram
      (fun w => indicator (ordEvent (setBad read S (P, m)) w.2)) ≤ capPair := by
  have h := unified_read_density read S 21 hS p hD i P m hi31 hm hσ
  simpa only [capPair, Nat.cast_ofNat] using h

/-- R1's row-32 density for the literal transcript, with the read and the bad
set abstract: the pair's bad set family has at most 21 elements. -/
theorem pair_row32_density {X : Type} (read : LiteralTranscript.Prefix → Option X)
    (S : X → Finset K) (hS : ∀ x, (S x).card ≤ 21)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 32) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (setBad read S P) v.2)) ≤
      capPair := by
  apply LiteralOrdinaryDensity.density P m (setBad read S P) capPair
  · omega
  · unfold capPair; nlinarith [perElem_nonneg]
  · rw [hround]
    exact pair_mean read S hS 32 le_rfl P

/-- R1's row-32 event is `setBad` with R1's read and `rhoBad`. -/
theorem rho_bad_eq (P : LiteralTranscript.Prefix) :
    LiteralRhoDensity.bad P = setBad LiteralRhoDensity.read
      (fun dq => QueryResidualBridge.rhoBad LiteralOpeningView.eK dq.1 dq.2) P := by
  funext v
  unfold LiteralRhoDensity.bad setBad
  cases LiteralRhoDensity.read P with
  | none => rfl
  | some dq => rfl

/-- R1's `LiteralRhoDensity.rho_mean`, same statement, from `pair_mean`. -/
theorem rho_mean_recovered (P : LiteralTranscript.Prefix) :
    mean (fun s : State => indicator
      (LiteralRhoDensity.bad P (SelectedChallengeMap.sigma 32 s))) ≤
      RhoSamplerBound.rhoCap := by
  rw [rho_bad_eq P, ← capPair_eq_rhoCap]
  exact pair_mean LiteralRhoDensity.read _
    (fun dq => QueryResidualBridge.rhoBad_card LiteralOpeningView.eK dq.1 dq.2) 32 le_rfl P

/-- R1's `LiteralRhoDensity.row32_density`, same statement, from `pair_row32_density`. -/
theorem row32_density_recovered (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 32) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (LiteralRhoDensity.bad P) v.2)) ≤
      RhoSamplerBound.rhoCap := by
  rw [rho_bad_eq P, ← capPair_eq_rhoCap]
  exact pair_row32_density LiteralRhoDensity.read _
    (fun dq => QueryResidualBridge.rhoBad_card LiteralOpeningView.eK dq.1 dq.2) P m hround

#print axioms selected_sigma_rho
#print axioms unified_row_density
#print axioms unified_read_density
#print axioms combining_unified_density
#print axioms round_unified_density
#print axioms pair_unified_density
#print axioms pair_row32_density
#print axioms rho_bad_eq
#print axioms rho_mean_recovered
#print axioms row32_density_recovered

end AspisRowDensity.Sampler
end
