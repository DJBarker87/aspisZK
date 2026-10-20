import GammaCandidateDecodedFieldRank
import R0C.ModuloField

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1GammaCaller.DigitsModel

open AspisR1
open AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound

/-- Candidate-only successful gamma output lands in a fixed finite set. -/
def candidateGammaHits (bad : Finset AspisWideTower.WideExact) (s : State) : Prop :=
  ∃ out : GammaWide,
    AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers (encodeState s) = .ok out ∧
    gammaWideToExact out ∈ bad

theorem candidate_gamma_hits_implies
    (bad : Finset AspisWideTower.WideExact) (s : State) :
    candidateGammaHits bad s → R0C.ModuloField.gamma s ∈ bad := by
  rintro ⟨out, hsample, hbad⟩
  obtain ⟨digits, hdecode, hcanonical, hvalue, hfield⟩ :=
    candidate_gamma_decode_fieldRank (encodeState s) out hsample
  have hrank : SourceSamplerByteRank.rank (encodeState s) =
      (R0C.ModuloField.blockRank s).val := by
    simp [SourceSamplerByteRank.rank, state_roundtrip]
  have hmodel : gammaWideToExact out = R0C.ModuloField.gamma s := by
    rw [hfield]
    simp [R0C.ModuloField.gamma, R0C.ModuloField.gammaNZ,
      R0C.ModuloField.nonzeroRank, R0C.ModuloField.positiveRanks,
      Equiv.trans_apply, hrank, R0C.ModuloCounting.reduce,
      AspisR1.SamplerMachineBounds.P, AspisCircleGroupOrder.P]
  rw [hmodel] at hbad
  exact hbad

theorem candidate_gamma_finite_bad_mass
    (bad : Finset AspisWideTower.WideExact) :
    mean (fun s : State => indicator (candidateGammaHits bad s)) ≤
      bad.card * (257 / (256^32 : ℚ)) := by
  apply (FS.mean_mono ?_).trans (R0C.ModuloField.gamma_event bad)
  intro s
  by_cases h : candidateGammaHits bad s
  · have hbad := candidate_gamma_hits_implies bad s h
    simp [indicator, h, hbad]
  · simp only [indicator, if_neg h]
    split_ifs <;> norm_num

#print axioms candidate_gamma_hits_implies
#print axioms candidate_gamma_finite_bad_mass

end AspisR1GammaCaller.DigitsModel
