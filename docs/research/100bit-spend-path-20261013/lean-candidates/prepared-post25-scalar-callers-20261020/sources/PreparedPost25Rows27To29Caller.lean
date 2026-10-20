import PreparedPost25TranscriptTransport
import GammaCandidateScalarTranscriptFieldRank
import Post25OrdinaryCandidateSourceModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1PublicPreparation.Post25Rows27To29Caller

open AspisR1PublicPreparation.Post25TranscriptTransport

abbrev CandidateOps := AspisR1Post25Transcript.SamplerOps

def ordinaryCandidateOps : CandidateOps :=
  AspisR1Post25Transcript.OrdinaryCandidateSourceModel.operations
    (fun _ => .div) (fun _ => .div) (fun _ => .div)

def post25CandidateOps : CandidateOps where
  gamma := AspisR1Post25Transcript.GammaCandidateSourceModel.gammaCandidateOps.gamma
  ordinary := ordinaryCandidateOps.ordinary
  qm31 := fun _ => .div
  embed := fun _ => .div

private theorem candidate_scalar_true_congr {H : Type}
    (ops₁ ops₂ : CandidateOps) (D : CandidateDigest H)
    (self : CandidateTranscript H) (row : U8) (payload : Slice U8)
    (hg : ∀ bytes, ops₁.gamma bytes = ops₂.gamma bytes) :
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₁ D self row payload true =
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₂ D self row payload true := by
  cases h : AspisR1Post25Transcript.transcript.Transcript.block D self row payload with
  | ok pair =>
      rcases pair with ⟨block, after⟩
      simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h, hg,
        AspisR1Post25Transcript.trace.value]
  | fail e => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]
  | div => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]

private theorem candidate_scalar_false_congr {H : Type}
    (ops₁ ops₂ : CandidateOps) (D : CandidateDigest H)
    (self : CandidateTranscript H) (row : U8) (payload : Slice U8)
    (ho : ∀ bytes, ops₁.ordinary bytes = ops₂.ordinary bytes) :
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₁ D self row payload false =
    AspisR1Post25Transcript.transcript.Transcript.scalar ops₂ D self row payload false := by
  cases h : AspisR1Post25Transcript.transcript.Transcript.block D self row payload with
  | ok pair =>
      rcases pair with ⟨block, after⟩
      simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h, ho,
        AspisR1Post25Transcript.trace.value]
  | fail e => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]
  | div => simp [AspisR1Post25Transcript.transcript.Transcript.scalar, h]

/-- A successful Prepared body with row callbacks installed via the explicit candidate
WideExact transport retains the actual row-27 gamma and rows-28/29 ordinary calls.
Its other Prepared boundaries are unchanged. -/
theorem prepare_success_rows27_29 {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : CurrentDigest H) (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (hprep : AspisR1PublicPreparation.PreparedModel.prepare
      (withCandidateScalars B post25CandidateOps) D sem v hash = .ok (.Ok out)) :
    ∃ start t1 t2 t3 inactiveBytes gamma kappa alpha0 gammaBlock kappaBlock alphaBlock,
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state v.variant = .ok start ∧
      (withCandidateScalars B post25CandidateOps).toBytes v.inactive = .ok inactiveBytes ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D start 27#u8 v.y1 true = .ok (gamma,t1) ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D t1 28#u8 (Array.to_slice inactiveBytes) false = .ok (kappa,t2) ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D t2 29#u8 v.round0 false = .ok (alpha0,t3) ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode (wideToCandidate gamma) =
        R0C.ModuloField.fieldRank ⟨
          AspisR1.SourceSamplerByteRank.rank gammaBlock %
            (AspisR1.SamplerMachineBounds.P ^ 8 - 1) + 1, by
          have hb := (AspisR1.SamplerNatModel.gammaDigits_value_bounds
            (AspisR1.SourceSamplerByteRank.rank_lt gammaBlock)).2
          rw [AspisR1.SamplerNatModel.gammaDigits_value
            (AspisR1.SourceSamplerByteRank.rank_lt gammaBlock)] at hb
          simpa [AspisR1.SamplerMachineBounds.P,
            AspisCircleGroupOrder.P] using hb⟩ ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode (wideToCandidate kappa) =
        R0C.ModuloField.ordinary (AspisV8R19.SqueezeOracleBridge.decodeState kappaBlock) ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode (wideToCandidate alpha0) =
        R0C.ModuloField.ordinary (AspisV8R19.SqueezeOracleBridge.decodeState alphaBlock) := by
  have hr := AspisR1PublicPreparation.PreparedReachability.prepare_success
    (withCandidateScalars B post25CandidateOps) D sem v hash out hprep
  rcases hr with ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,
    hseed,hgamma,hbytes,hkappa,halpha0,_tail⟩
  have hcGamma := scalar_success_candidate_ops B post25CandidateOps D start
    27#u8 v.y1 true gamma t1 hgamma
  have hGammaEq := candidate_scalar_true_congr post25CandidateOps
    AspisR1Post25Transcript.GammaCandidateSourceModel.gammaCandidateOps
    (digestToCandidate D) (transcriptToCandidate start) 27#u8 v.y1
    (by intro bytes; rfl)
  have hCandidateGamma := hGammaEq.symm.trans hcGamma
  obtain ⟨gammaBlock,_absorbed,_nextState,_sample,_digits,_habs,_hread,_hstate,
      _hafter,_hgamma,_hcanonical,_hscalar,hgammaField⟩ :=
    AspisR1Post25Transcript.GammaCandidateSourceModel.scalar_true_success_fieldRank
      (digestToCandidate D) (transcriptToCandidate start) (transcriptToCandidate t1)
      v.y1 (wideToCandidate gamma) hCandidateGamma
  have hcKappa := scalar_success_candidate_ops B post25CandidateOps D t1
    28#u8 (Array.to_slice inactiveBytes) false kappa t2 hkappa
  have hOrdEq := candidate_scalar_false_congr post25CandidateOps ordinaryCandidateOps
    (digestToCandidate D) (transcriptToCandidate t1) 28#u8 (Array.to_slice inactiveBytes)
    (by intro bytes; rfl)
  have hCandidateKappa := hOrdEq.symm.trans hcKappa
  have htag28 : (160#u8 + 28#u8 : Result U8) = .ok 188#u8 := by
    have hs : (160#u8 + 28#u8 : Result U8) ⦃z => z.val = 188⦄ := by
      apply UScalar.add_spec
      change 160 + 28 ≤ UScalar.max UScalarTy.U8
      norm_num [UScalar.max_UScalarTy_U8_eq, U8.max, U8.numBits]
    obtain ⟨tag, ht, hv⟩ := WP.spec_imp_exists hs
    have he : tag = 188#u8 := UScalar.eq_of_val_eq (by simpa using hv)
    rw [he] at ht
    exact ht
  obtain ⟨kappaBlock,_absorbedK,_stateK,_habsK,_hreadK,_hstateK,_hafterK,hkappaField⟩ :=
    AspisR1Post25Transcript.OrdinaryCandidateSourceModel.scalar_model_success
      (digestToCandidate D) (fun _ => .div) (fun _ => .div) (fun _ => .div)
      (transcriptToCandidate t1) (transcriptToCandidate t2) 28#u8 188#u8
      (Array.to_slice inactiveBytes) (wideToCandidate kappa) htag28 hCandidateKappa
  have hcAlpha := scalar_success_candidate_ops B post25CandidateOps D t2
    29#u8 v.round0 false alpha0 t3 halpha0
  have hOrdEq2 := candidate_scalar_false_congr post25CandidateOps ordinaryCandidateOps
    (digestToCandidate D) (transcriptToCandidate t2) 29#u8 v.round0
    (by intro bytes; rfl)
  have hCandidateAlpha := hOrdEq2.symm.trans hcAlpha
  have htag29 : (160#u8 + 29#u8 : Result U8) = .ok 189#u8 := by
    have hs : (160#u8 + 29#u8 : Result U8) ⦃z => z.val = 189⦄ := by
      apply UScalar.add_spec
      change 160 + 29 ≤ UScalar.max UScalarTy.U8
      norm_num [UScalar.max_UScalarTy_U8_eq, U8.max, U8.numBits]
    obtain ⟨tag, ht, hv⟩ := WP.spec_imp_exists hs
    have he : tag = 189#u8 := UScalar.eq_of_val_eq (by simpa using hv)
    rw [he] at ht
    exact ht
  obtain ⟨alphaBlock,_absorbedA,_stateA,_habsA,_hreadA,_hstateA,_hafterA,halphaField⟩ :=
    AspisR1Post25Transcript.OrdinaryCandidateSourceModel.scalar_model_success
      (digestToCandidate D) (fun _ => .div) (fun _ => .div) (fun _ => .div)
      (transcriptToCandidate t2) (transcriptToCandidate t3) 29#u8 189#u8
      v.round0 (wideToCandidate alpha0) htag29 hCandidateAlpha
  exact ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,gammaBlock,kappaBlock,
    alphaBlock,hseed,hbytes,hgamma,hkappa,halpha0,hgammaField,hkappaField,halphaField⟩

#print axioms prepare_success_rows27_29

end AspisR1PublicPreparation.Post25Rows27To29Caller
