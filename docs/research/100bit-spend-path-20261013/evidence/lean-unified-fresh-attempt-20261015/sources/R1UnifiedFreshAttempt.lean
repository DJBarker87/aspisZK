import R1UnifiedEventDensity
import R1FreshAttemptBound

/-! Apply the existing row-classifier density bounds to the explicit adaptive
fresh-answer interpreter. This is a fresh-row-sampler result only; it does not
conclude acceptance, source correspondence, or a memoized-ROM bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedFreshAttempt

open FS FS2 FS2.Duplex R0C.V3
open AspisCircleGroupOrder AspisR1.MatchingSupport
open R0P R0P.SemSource R0P.Mask R0P.SemD3Glue
open AspisV8PairedCommitment AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
open TranscriptView

variable {M K : Type} {L : Nat} {Pf : Type}
  [Field K] [Fintype K]
  {Sfield : Fin 29 → Subfield SemE} {F : Subfield SemE}
  [Algebra (ZMod P) SemE]

theorem thirty_three_rows_lt
    (p : Params M SemE L) (hD : 5 ≤ p.D)
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
    (choose : UnifiedSampler.Prefix M SemE L → Table (Addr L) State → Message M)
    (update : UnifiedSampler.Prefix M SemE L → Message M → Table (Addr L) State →
      View (Addr L) State (Challenge SemE) → Table (Addr L) State)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State) :
    FreshAttemptBound.hitMass p hD
      (UnifiedEventDensity.classifier pack semanticDecoded openingDecoded queryDecoded
        rhoDecoded iota rhoOf) choose update 33 (FS.emptyPrefix pub) T <
      1 / (2^100 : ℚ) := by
  apply FreshAttemptBound.thirty_three_hitMass_lt p hD
    (UnifiedEventDensity.classifier pack semanticDecoded openingDecoded queryDecoded
      rhoDecoded iota rhoOf) choose update
  · intro P m table hlen
    exact UnifiedEventDensity.density_bound p hD pack semanticDecoded hsigmaSem
      openingDecoded inputOpening outputOpening outputOpeningNZ hσ27 hσ28 hσ29 hσ30
      queryDecoded rhoDecoded iota rhoOf inputRho outputRho hσ32
      table P.rounds.length P m (by omega) rfl

#print axioms thirty_three_rows_lt

end AspisR1.UnifiedFreshAttempt
end
