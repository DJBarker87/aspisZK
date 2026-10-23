import AspisR1PublicPreparation.Funs
import ExtractedDigest32SamplerTransport

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1ActualSemanticValidatedCanonicalV1
open _root_.AspisR1PublicPreparation

private theorem bind_success_inv {A B : Type} (r : Result A)
    (f : A → Result B) (b : B)
    (h : (do let a ← r; f a) = .ok b) :
    ∃ a, r = .ok a ∧ f a = .ok b := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Reflect the sampler success belonging to this exact successful source method. -/
theorem semantic_validated_success_has_sampler
    {H : Type} (digest : aspis_core.Digest32 H)
    (transcript transcript' : r1_wire.SemanticTranscript H)
    (record : r1_wire.ValidatedRecord) (q : aspis_core.field.QM31)
    (h : r1_wire.SemanticTranscript.semantic_validated digest transcript record =
      .ok (.Ok q, transcript')) :
    ∃ block : Array Std.U8 32#usize, sampler.qm31_sample block = .ok q := by
  unfold r1_wire.SemanticTranscript.semantic_validated at h
  simp only [r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed, bind_tc_ok] at h
  split at h
  · cases h
  · obtain ⟨⟨r,t⟩,hs,h⟩ := bind_success_inv _ _ _ h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame] at h
    | Ok block =>
      change (do
        let value ← sampler.qm31_sample block
        ok (core.result.Result.Ok value,t)) =
          ok (core.result.Result.Ok q,transcript') at h
      obtain ⟨value,hvalue,hresult⟩ := bind_success_inv _ _ _ h
      have heq := Result.ok.inj hresult
      have hv : value = q := core.result.Result.Ok.inj (congrArg Prod.fst heq)
      exact ⟨block,hv ▸ hvalue⟩

/-- Canonicality follows from the existing universal byte sampler theorem;
there is no restriction on the actual digest-produced block. -/
theorem semantic_validated_success_canonical
    {H : Type} (digest : aspis_core.Digest32 H)
    (transcript transcript' : r1_wire.SemanticTranscript H)
    (record : r1_wire.ValidatedRecord) (q : aspis_core.field.QM31)
    (h : r1_wire.SemanticTranscript.semantic_validated digest transcript record =
      .ok (.Ok q, transcript')) :
    AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
        (AspisR1PublicPreparation.SamplerTransport.toOld q)) := by
  obtain ⟨block,hs⟩ := semantic_validated_success_has_sampler
    digest transcript transcript' record q h
  obtain ⟨q0,h0,hc,_⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total block
  have heq : q0 = q := Result.ok.inj (h0.symm.trans hs)
  exact heq ▸ hc

#print axioms semantic_validated_success_has_sampler
#print axioms semantic_validated_success_canonical
end AspisR1ActualSemanticValidatedCanonicalV1
