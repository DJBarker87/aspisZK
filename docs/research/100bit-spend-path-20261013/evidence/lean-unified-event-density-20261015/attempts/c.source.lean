import R1UnifiedSemanticDensity
import R1UnifiedOpeningDensity
import R1UnifiedQueryDensity
import R1UnifiedRhoDensity
import R1UnifiedCausalBound
import R1PerAttemptEnvelope

/-! One explicit row-dispatch classifier reuses the existing independent-row
bounds. Decoder callbacks, field embeddings, and sampler identities remain
supplied parameters; no acceptance, source, or extraction bridge is proved. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedEventDensity

open FS FS2 FS2.Duplex R0C.V3
open AspisCircleGroupOrder AspisR1.MatchingSupport
open R0P R0P.SemSource R0P.Mask
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open TranscriptView

variable {M K : Type} {L : Nat} {Pf : Type}
  [Field K] [Fintype K]
  {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE}
  [Algebra (ZMod P) SemE]

/-- The row dispatch uses the 25 semantic prefix rows, four opening rows,
the query row, and rho row. Rows 25 and 26 are classified as false here. -/
def classifier
    (pack : PackBasis F)
    (semanticDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedSemanticDensity.DecodedSemantic Sfield))
    (openingDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedOpeningDensity.DecodedOpening SemE))
    (queryDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (Finset (Fin 262144)))
    (rhoDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (MatchingSupport.Data SemE ×
        (Fin 22 → Fin 262144)))
    (iota : K →+* SemE) (rhoOf : SemE → K)
    (P : UnifiedSampler.Prefix M SemE L) (m : Message M)
    (T : Table (Addr L) State) (ch : Challenge SemE) : Prop :=
  if P.rounds.length < 25 then
    UnifiedSemanticDensity.semanticBad pack semanticDecoded P m T ch
  else if P.rounds.length = 27 ∨ P.rounds.length = 28 ∨
      P.rounds.length = 29 ∨ P.rounds.length = 30 then
    UnifiedOpeningDensity.openingBad openingDecoded P m T ch
  else if P.rounds.length = 31 then
    UnifiedQueryDensity.queryBad queryDecoded P m T ch
  else if P.rounds.length = 32 then
    UnifiedRhoDensity.rhoBad iota rhoOf rhoDecoded P m T ch
  else False

private theorem envelope_nonneg : 0 ≤ PerAttemptEnvelope.B := by
  unfold PerAttemptEnvelope.B
  positivity

private theorem independentMean_zero {I A O : Type} [Fintype A] [Nonempty A]
    (q : Program I A O) : independentMean q (fun _ => (0 : ℚ)) = 0 := by
  induction q with
  | done _ => rfl
  | ask i k ih =>
      simp only [independentMean]
      rw [show (fun a => independentMean (k a) (fun _ => (0 : ℚ))) =
        fun _ => (0 : ℚ) from funext fun a => ih a]
      simp [mean_const]

theorem density_bound (p : Params M SemE L) (hD : 5 ≤ p.D)
    (pack : PackBasis F)
    (semanticDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedSemanticDensity.DecodedSemantic Sfield))
    (hsigmaSem : ∀ i, i < 25 → ∀ s : State, p.σ i s = semChal s)
    (openingDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedOpeningDensity.DecodedOpening SemE))
    (inputOpening : State ≃ Fin (2^256)) (outputOpening : Fin (P^8) ≃ SemE)
    (outputOpeningNZ : Fin (P^8 - 1) ≃ {x : SemE // x ≠ 0})
    (hσ27 : ∀ s : State,
      p.σ 27 s = OpeningSamplerBound.gammaSample inputOpening outputOpeningNZ s)
    (hσ28 : ∀ s : State, p.σ 28 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (hσ29 : ∀ s : State, p.σ 29 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (hσ30 : ∀ s : State, p.σ 30 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (queryDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (Finset (Fin 262144)))
    (rhoDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (MatchingSupport.Data SemE ×
        (Fin 22 → Fin 262144)))
    (iota : K →+* SemE) (rhoOf : SemE → K)
    (inputRho : State ≃ Fin (2^256)) (outputRho : Fin (P^4) ≃ K)
    (hσ32 : ∀ s : State,
      rhoOf (p.σ 32 s) = outputRho
        (R0C.ModuloCounting.reduce (by norm_num [AspisCircleGroupOrder.P])
          (inputRho s))) :
    ∀ (T : Table (Addr L) State) (i : Nat) (Pfx : UnifiedSampler.Prefix M SemE L)
      (m : Message M), i < 33 → Pfx.rounds.length = i →
      independentMean (UnifiedSampler.samp p hD i Pfx m).toProgram
        (fun w => indicator (classifier pack semanticDecoded openingDecoded queryDecoded
          rhoDecoded iota rhoOf Pfx m T w.2)) ≤ PerAttemptEnvelope.B := by
  intro T i Pfx m hi hround
  by_cases hi25 : i < 25
  · have hlen : Pfx.rounds.length < 25 := by omega
    have hsem := UnifiedSemanticDensity.semantic_density_bound p hD pack
      semanticDecoded hsigmaSem T i Pfx m hround
    have hrow : UnifiedSemanticDensity.rowBudget i ≤ PerAttemptEnvelope.B := by
      unfold UnifiedSemanticDensity.rowBudget
      split_ifs with hi25'
      · exact PerAttemptEnvelope.semantic_row_le ⟨i, hi25'⟩
      · exact envelope_nonneg
    simpa [classifier, hlen] using hsem.trans hrow
  · by_cases hi27 : i = 27
    · have hlen : Pfx.rounds.length = 27 := by omega
      have hopen := UnifiedOpeningDensity.opening_density_bound p hD openingDecoded
        inputOpening outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30 T i Pfx m hi hround
      have hcap := PerAttemptEnvelope.opening_cap_le
      simpa [classifier, hlen] using hopen.trans hcap
    · by_cases hi28 : i = 28
      · have hlen : Pfx.rounds.length = 28 := by omega
        have hopen := UnifiedOpeningDensity.opening_density_bound p hD openingDecoded
          inputOpening outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30 T i Pfx m hi hround
        simpa [classifier, hlen] using hopen.trans PerAttemptEnvelope.opening_cap_le
      · by_cases hi29 : i = 29
        · have hlen : Pfx.rounds.length = 29 := by omega
          have hopen := UnifiedOpeningDensity.opening_density_bound p hD openingDecoded
            inputOpening outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30 T i Pfx m hi hround
          simpa [classifier, hlen] using hopen.trans PerAttemptEnvelope.opening_cap_le
        · by_cases hi30 : i = 30
          · have hlen : Pfx.rounds.length = 30 := by omega
            have hopen := UnifiedOpeningDensity.opening_density_bound p hD openingDecoded
              inputOpening outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30 T i Pfx m hi hround
            simpa [classifier, hlen] using hopen.trans PerAttemptEnvelope.opening_cap_le
          · by_cases hi31 : i = 31
            · have hlen : Pfx.rounds.length = 31 := by omega
              have hquery := UnifiedQueryDensity.query_density_bound p hD queryDecoded
                T i Pfx m hi hround
              simpa [classifier, hlen] using hquery.trans PerAttemptEnvelope.query_cap_le
            · by_cases hi32 : i = 32
              · have hlen : Pfx.rounds.length = 32 := by omega
                have hrho := UnifiedRhoDensity.rho_density_bound p hD iota rhoOf rhoDecoded
                  inputRho outputRho hσ32 T i Pfx m hi hround
                simpa [classifier, hlen] using hrho.trans PerAttemptEnvelope.rho_cap_le
              · have hfalse : ∀ ch,
                    classifier pack semanticDecoded openingDecoded queryDecoded rhoDecoded
                      iota rhoOf Pfx m ch = False := by
                  intro ch
                  unfold classifier
                  rw [hround]
                  simp [hi25, hi27, hi28, hi29, hi30, hi31, hi32]
                have hzero : (fun w : View (Addr L) State (Challenge SemE) =>
                    indicator (classifier pack semanticDecoded openingDecoded queryDecoded
                      rhoDecoded iota rhoOf Pfx m T w.2)) = fun _ => (0 : ℚ) := by
                  funext w
                  rw [hfalse w.2]
                  exact indicator_false
                rw [hzero, independentMean_zero]
                exact envelope_nonneg

variable {M K : Type} {L : Nat} {Pf : Type}
  [Field K] [Fintype K]
  {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE}
  [Algebra (ZMod P) SemE]

theorem first_hit_bound (p : Params M SemE L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L)
    (pack : PackBasis F)
    (semanticDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedSemanticDensity.DecodedSemantic Sfield))
    (hsigmaSem : ∀ i, i < 25 → ∀ s : State, p.σ i s = semChal s)
    (openingDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (UnifiedOpeningDensity.DecodedOpening SemE))
    (inputOpening : State ≃ Fin (2^256)) (outputOpening : Fin (P^8) ≃ SemE)
    (outputOpeningNZ : Fin (P^8 - 1) ≃ {x : SemE // x ≠ 0})
    (hσ27 : ∀ s : State,
      p.σ 27 s = OpeningSamplerBound.gammaSample inputOpening outputOpeningNZ s)
    (hσ28 : ∀ s : State, p.σ 28 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (hσ29 : ∀ s : State, p.σ 29 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (hσ30 : ∀ s : State, p.σ 30 s = OpeningSamplerBound.sample inputOpening outputOpening s)
    (queryDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (Finset (Fin 262144)))
    (rhoDecoded : UnifiedSampler.Prefix M SemE L → Message M →
      Table (Addr L) State → Option (MatchingSupport.Data SemE ×
        (Fin 22 → Fin 262144)))
    (iota : K →+* SemE) (rhoOf : SemE → K)
    (inputRho : State ≃ Fin (2^256)) (outputRho : Fin (P^4) ≃ K)
    (hσ32 : ∀ s : State,
      rhoOf (p.σ 32 s) = outputRho
        (R0C.ModuloCounting.reduce (by norm_num [AspisCircleGroupOrder.P])
          (inputRho s)))
    (q : Program (Addr L) State (Pf × Bool)) (t : Table (Addr L) State)
    (N : Nat) (hN : FirstReadsBound q t N) :
    lazyMean q t (fun v =>
      indicator (hitsChain3 (UnifiedDecoder.decode p hD pub)
        (classifier pack semanticDecoded openingDecoded queryDecoded rhoDecoded iota rhoOf) t v.1)) ≤
      (N : ℚ) * PerAttemptEnvelope.B := by
  exact UnifiedCausalBound.first_hit_bound p hD pub
    (classifier pack semanticDecoded openingDecoded queryDecoded rhoDecoded iota rhoOf)
    PerAttemptEnvelope.B envelope_nonneg
    (density_bound p hD pack semanticDecoded hsigmaSem openingDecoded inputOpening
      outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30 queryDecoded rhoDecoded iota rhoOf
      inputRho outputRho hσ32) q t N hN

#print axioms density_bound
#print axioms first_hit_bound

end AspisR1.UnifiedEventDensity
end
