import S4ResumeGammaActualCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeAlphaSourceCanonicalV1
open AspisR1Stage2
open AspisR1.OraclePortCkptAbiSourceFields
open AspisR1S4ReaderEActualWideCanonicalV1

/-- The same successful source resume with its concrete strict Reader.e
installed supplies the exact two folding challenges, their actual read calls
and all eight canonical limb bounds. No sampler law or independent challenge
canonicality is assumed. The raw read/interface remains the existing source
operation boundary; this is not a whole-runtime refinement claim. -/
theorem resume_success_alpha_sources_canonical
    (ops : ResumeOps) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (h : verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
      D bytes proof publicInput v hash = .ok (.Ok (p,acc))) :
    ∃ (a0 a1 : aspis_core.field.wide_exact.WideExact) (r0 r1 r2 : verifier.Reader),
      p.alpha = Array.make 2#usize [a0,a1] ∧
      readerE ops.raw r0 = .ok (.Ok a0,r1) ∧
      readerE ops.raw r1 = .ok (.Ok a1,r2) ∧
      currentWideCanonical a0 ∧ currentWideCanonical a1 := by
  obtain ⟨fields⟩ := successful_fields (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
    D bytes proof publicInput v hash p acc h
  refine ⟨fields.alpha0,fields.alpha1,fields.rKappa,fields.rAlpha0,fields.rAlpha1,
    fields.alpha,fields.alpha0Read,fields.alpha1Read,?_,?_⟩
  · exact readerE_success_canonical ops.raw fields.rKappa fields.alpha0
      fields.rAlpha0 fields.alpha0Read
  · exact readerE_success_canonical ops.raw fields.rAlpha0 fields.alpha1
      fields.rAlpha1 fields.alpha1Read

#print axioms resume_success_alpha_sources_canonical
end AspisR1S9ResumeAlphaSourceCanonicalV1
