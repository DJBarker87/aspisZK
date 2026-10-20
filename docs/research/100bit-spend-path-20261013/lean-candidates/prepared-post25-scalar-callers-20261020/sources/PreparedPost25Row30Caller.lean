import PreparedPost25TranscriptTransport
import Post25OrdinaryCandidateSourceModel

set_option autoImplicit false
open Aeneas Aeneas.Std Result WP

namespace AspisR1PublicPreparation.Post25Row30Caller

open AspisR1PublicPreparation.Post25TranscriptTransport

abbrev CandidateOps := AspisR1Post25Transcript.SamplerOps

def ordinaryCandidateOps : CandidateOps :=
  AspisR1Post25Transcript.OrdinaryCandidateSourceModel.operations
    (fun _ => .div) (fun _ => .div) (fun _ => .div)

def post25CandidateOps : CandidateOps where
  gamma := fun _ => .div
  ordinary := ordinaryCandidateOps.ordinary
  qm31 := fun _ => .div
  embed := fun _ => .div

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

/-- The actual two-fold Prepared path's row-30 scalar call is the retained ordinary
candidate operation under the explicit WideExact record transport. -/
theorem prepare_success_row30 {H : Type}
    (B : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (D : CurrentDigest H) (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (v : AspisR1PublicPreparation.verifier.View) (hash : H)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (hfolds : AspisR1PublicPreparation.transport.Variant.folds v.variant = .ok 2#usize)
    (hprep : AspisR1PublicPreparation.PreparedModel.prepare
      (withCandidateScalars B post25CandidateOps) D sem v hash = .ok (.Ok out)) :
    ∃ start t1 t2 t3 inactiveBytes gamma kappa alpha0 root bytes1 bytes2 alpha1 afterAlpha block30,
      AspisR1PublicPreparation.transcript.Transcript.new D hash sem.transcript.state v.variant = .ok start ∧
      (withCandidateScalars B post25CandidateOps).toBytes v.inactive = .ok inactiveBytes ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D start 27#u8 v.y1 true = .ok (gamma,t1) ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D t1 28#u8 (Array.to_slice inactiveBytes) false = .ok (kappa,t2) ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D t2 29#u8 v.round0 false = .ok (alpha0,t3) ∧
      core.option.Option.unwrap v.folded_root = .ok root ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8
        (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root) = .ok bytes1 ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1 = .ok bytes2 ∧
      AspisR1PublicPreparation.PreparedModel.scalar
        (withCandidateScalars B post25CandidateOps) D t3 30#u8
        (alloc.vec.Vec.deref bytes2) false = .ok (alpha1,afterAlpha) ∧
      AspisR1Post25Transcript.OrdinaryCandidateSourceModel.decode (wideToCandidate alpha1) =
        R0C.ModuloField.ordinary
          (AspisV8R19.SqueezeOracleBridge.decodeState block30) := by
  have hr := AspisR1PublicPreparation.PreparedReachability.prepare_success
    (withCandidateScalars B post25CandidateOps) D sem v hash out hprep
  rcases hr with ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,
    hseed,hgamma,hbytes,hkappa,halpha0,htail⟩
  cases htail with
  | single hs _ => simp [hfolds] at hs
  | double hs root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1 _ =>
      have hc := scalar_success_candidate_ops B post25CandidateOps D t3
        30#u8 (alloc.vec.Vec.deref bytes2) false alpha1 afterAlpha halpha1
      have heq := candidate_scalar_false_congr post25CandidateOps ordinaryCandidateOps
        (digestToCandidate D) (transcriptToCandidate t3) 30#u8
        (alloc.vec.Vec.deref bytes2) (by intro bytes; rfl)
      have hCand := heq.symm.trans hc
      have htag30 : (160#u8 + 30#u8 : Result U8) = .ok 190#u8 := by
        have hs' : (160#u8 + 30#u8 : Result U8) ⦃z => z.val = 190⦄ := by
          apply UScalar.add_spec
          change 160 + 30 ≤ UScalar.max UScalarTy.U8
          norm_num [UScalar.max_UScalarTy_U8_eq, U8.max, U8.numBits]
        obtain ⟨tag, ht, hv⟩ := WP.spec_imp_exists hs'
        have he : tag = 190#u8 := UScalar.eq_of_val_eq (by simpa using hv)
        rw [he] at ht
        exact ht
      obtain ⟨block30,_absorbed,_state,_habs,_hread,_hstate,_hafter,hfield⟩ :=
        AspisR1Post25Transcript.OrdinaryCandidateSourceModel.scalar_model_success
          (digestToCandidate D) (fun _ => .div) (fun _ => .div) (fun _ => .div)
          (transcriptToCandidate t3) (transcriptToCandidate afterAlpha)
          30#u8 190#u8 (alloc.vec.Vec.deref bytes2) (wideToCandidate alpha1)
          htag30 hCand
      exact ⟨start,t1,t2,t3,inactiveBytes,gamma,kappa,alpha0,root,bytes1,bytes2,
        alpha1,afterAlpha,block30,hseed,hbytes,hgamma,hkappa,halpha0,hroot,hbytes1,
        hbytes2,halpha1,hfield⟩

#print axioms prepare_success_row30

end AspisR1PublicPreparation.Post25Row30Caller
