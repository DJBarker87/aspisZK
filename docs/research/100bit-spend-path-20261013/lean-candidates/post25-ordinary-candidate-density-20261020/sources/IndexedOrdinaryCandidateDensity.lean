import IndexedCandidateOrdinaryRetainedBridgeV5
set_option autoImplicit false
noncomputable section
namespace AspisR1.IndexedOrdinaryCandidateDensity
open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3
attribute [local instance] Classical.propDecidable

theorem encoded_output (s : State) :
    ∃ value : CandidateWide,
      sampler.ordinary_sample (encodeState s) = .ok value ∧
      candidateWideToExact value = R0C.ModuloField.ordinary s := by
  obtain ⟨value,hvalue,hfield⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV5.ordinary_sample_candidate_eq_fieldRank
      (encodeState s)
  refine ⟨value,hvalue,?_⟩
  simpa only [AspisR1.SourceSamplerByteRank.rank, state_roundtrip,
    R0C.ModuloField.ordinary, R0C.ModuloCounting.reduce] using hfield

def hits (s : State) (y : AspisWideTower.WideExact) : Prop :=
  ∃ value : CandidateWide,
    sampler.ordinary_sample (encodeState s) = .ok value ∧ candidateWideToExact value = y

theorem hits_iff (s : State) (y : AspisWideTower.WideExact) :
    hits s y ↔ R0C.ModuloField.ordinary s = y := by
  obtain ⟨value,hvalue,hmodel⟩ := encoded_output s
  constructor
  · rintro ⟨v,hv,heq⟩
    have hsame : v = value := Result.ok.inj (hv.symm.trans hvalue)
    subst v
    exact hmodel.symm.trans heq
  · intro heq
    exact ⟨value,hvalue,hmodel.trans heq⟩

theorem atom_mass (y : AspisWideTower.WideExact) :
    mean (fun s : State => indicator (hits s y)) ≤ 257 / (256^32 : ℚ) := by
  have he := mean_congr (fun s : State => FS.indicator_iff (hits_iff s y))
  exact he.le.trans (R0C.ModuloField.ordinary_mass_257 y)

def hitsBad (s : State) (bad : Finset AspisWideTower.WideExact) : Prop :=
  ∃ value : CandidateWide,
    sampler.ordinary_sample (encodeState s) = .ok value ∧ candidateWideToExact value ∈ bad

theorem hitsBad_iff (s : State) (bad : Finset AspisWideTower.WideExact) :
    hitsBad s bad ↔ R0C.ModuloField.ordinary s ∈ bad := by
  obtain ⟨value,hvalue,hmodel⟩ := encoded_output s
  constructor
  · rintro ⟨v,hv,hbad⟩
    have hsame : v = value := Result.ok.inj (hv.symm.trans hvalue)
    subst v
    rwa [hmodel] at hbad
  · intro hbad
    exact ⟨value,hvalue,by rwa [hmodel]⟩

theorem finite_bad_mass (bad : Finset AspisWideTower.WideExact) :
    mean (fun s : State => indicator (hitsBad s bad)) ≤
      bad.card * (257 / (256^32 : ℚ)) := by
  have he := mean_congr (fun s : State => FS.indicator_iff (hitsBad_iff s bad))
  exact he.le.trans (R0C.ModuloField.ordinary_event bad)
#print axioms encoded_output
#print axioms hits_iff
#print axioms atom_mass
#print axioms hitsBad_iff
#print axioms finite_bad_mass
end AspisR1.IndexedOrdinaryCandidateDensity
end
