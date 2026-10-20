import GammaCandidateDecodedFieldRank
import Post25OrdinaryCandidateSourceModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Post25Transcript.GammaCandidateSourceModel

open AspisR1GammaCaller.DigitsModel
open AspisR1Post25Transcript.OrdinaryCandidateSourceModel

abbrev Bytes32 := Array U8 32#usize
abbrev GammaWide := AspisR1GammaCaller.field.WideExact
abbrev CandidateWide := AspisR1Post25Sampler.field.WideExact
abbrev E := aspis_core.field.WideExact

private def gammaToCandidate (v : GammaWide) : CandidateWide :=
  ⟨⟨⟨v.c0.c0.a, v.c0.c0.b⟩, ⟨v.c0.c1.a, v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a, v.c1.c0.b⟩, ⟨v.c1.c1.a, v.c1.c1.b⟩⟩⟩

def gammaCandidateOps : SamplerOps where
  gamma := fun block => do
    let value ← AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block
    .ok (fromWide (gammaToCandidate value))
  ordinary := fun _ => .div
  qm31 := fun _ => .div
  embed := fun _ => .div

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem decode_gamma_candidate (v : GammaWide) :
    OrdinaryCandidateSourceModel.decode
        (fromWide (gammaToCandidate v)) = gammaWideToExact v := by
  unfold OrdinaryCandidateSourceModel.decode
  simp only [toWide_fromWide]
  apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

theorem scalar_true_success_fieldRank {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (payload : Slice U8)
    (out : E)
    (h : transcript.Transcript.scalar gammaCandidateOps D self 27#u8 payload true =
      .ok (out, after)) :
    ∃ block absorbed nextState sample digits,
      D.digest self.hash
        (TranscriptSuccess.absorbParts self.state 187#u8 payload) = .ok absorbed ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 1#u8) = .ok block ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 2#u8) = .ok nextState ∧
      after = {self with state := nextState} ∧
      AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block = .ok sample ∧
      Canonical digits ∧
      AspisR1.SamplerAddDigits.digitsValue AspisR1.SamplerMachineBounds.P (values digits) =
        AspisR1.SourceSamplerByteRank.rank block %
          (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1 ∧
      OrdinaryCandidateSourceModel.decode out =
        R0C.ModuloField.fieldRank ⟨
          AspisR1.SourceSamplerByteRank.rank block %
            (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1, by
          have hb := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
            (AspisR1.SourceSamplerByteRank.rank_lt block)).2
          rw [AspisR1.SamplerNatModel.gammaDigits_value
            (AspisR1.SourceSamplerByteRank.rank_lt block)] at hb
          simpa [AspisR1.SamplerMachineBounds.P,
            AspisCircleGroupOrder.P] using hb⟩ := by
  have htag : (160#u8 + 27#u8 : Result U8) = .ok 187#u8 := by
    have hs : (160#u8 + 27#u8 : Result U8) ⦃z => z.val = 187⦄ := by
      apply UScalar.add_spec
      change 160 + 27 ≤ UScalar.max UScalarTy.U8
      norm_num [UScalar.max_UScalarTy_U8_eq, U8.max, U8.numBits]
    obtain ⟨tag, ht, hv⟩ := WP.spec_imp_exists hs
    have he : tag = 187#u8 := UScalar.eq_of_val_eq (by simpa using hv)
    rw [he] at ht
    exact ht
  obtain ⟨block, hblock, hsample⟩ :=
    TranscriptSuccess.scalar_success gammaCandidateOps D self after 27#u8 payload true out h
  obtain ⟨absorbed, nextState, habs, hread, hstate, hafter⟩ :=
    TranscriptSuccess.block_success D self after 27#u8 187#u8 payload block htag hblock
  change gammaCandidateOps.gamma block = .ok out at hsample
  change (do
      let value ← AspisR1GammaCaller.sampler.gamma_sample candidateGammaHelpers block
      .ok (fromWide (gammaToCandidate value))) = .ok out at hsample
  obtain ⟨sample, hgamma, hvalue⟩ := bind_success _ _ _ hsample
  obtain ⟨digits, _hdecoded, hcanonical, hscalar, hfield⟩ :=
    candidate_gamma_decode_fieldRank block sample hgamma
  have hout : fromWide (gammaToCandidate sample) = out := Result.ok.inj hvalue
  refine ⟨block, absorbed, nextState, sample, digits, habs, hread, hstate, hafter,
    hgamma, hcanonical, hscalar, ?_⟩
  calc
    OrdinaryCandidateSourceModel.decode out =
        OrdinaryCandidateSourceModel.decode (fromWide (gammaToCandidate sample)) := by
      rw [hout]
    _ = gammaWideToExact sample := decode_gamma_candidate sample
    _ = R0C.ModuloField.fieldRank ⟨
        AspisR1.SourceSamplerByteRank.rank block %
          (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1, by
        have hb := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
          (AspisR1.SourceSamplerByteRank.rank_lt block)).2
        rw [AspisR1.SamplerNatModel.gammaDigits_value
          (AspisR1.SourceSamplerByteRank.rank_lt block)] at hb
        simpa [AspisR1.SamplerMachineBounds.P,
          AspisCircleGroupOrder.P] using hb⟩ := hfield

#print axioms scalar_true_success_fieldRank

end AspisR1Post25Transcript.GammaCandidateSourceModel
