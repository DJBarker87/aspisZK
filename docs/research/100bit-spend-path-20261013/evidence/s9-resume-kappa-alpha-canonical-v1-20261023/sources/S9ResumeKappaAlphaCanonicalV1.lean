import S4ResumeGammaActualCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeKappaAlphaCanonicalV1
open AspisR1Stage2
open AspisR1.OraclePortCkptAbiSourceFields
open AspisR1S4ReaderEActualWideCanonicalV1
/-- The SAME successful checkpoint resume supplies kappa and both stored
fold challenges from actual strict Reader.e successes, with the exact
Prepared alpha array. No separate read or canonicality premise is supplied. -/
theorem resume_kappa_alpha_canonical
    (ops : ResumeOps) {H : Type} (digestInst : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (h : verifier.resumeWithOps (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
      digestInst bytes proof public1 v hash=.ok (.Ok (p,acc))) :
    currentWideCanonical p.kappa ∧
    ∃ a0 a1 : aspis_core.field.wide_exact.WideExact,
      p.alpha=Array.make 2#usize [a0,a1] ∧
      currentWideCanonical a0 ∧ currentWideCanonical a1 := by
  obtain ⟨fields⟩ := successful_fields
    (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)
    digestInst bytes proof public1 v hash p acc h
  have hk := readerE_success_canonical ops.raw fields.rGamma p.kappa
    fields.rKappa fields.kappaRead
  have h0 := readerE_success_canonical ops.raw fields.rKappa fields.alpha0
    fields.rAlpha0 fields.alpha0Read
  have h1 := readerE_success_canonical ops.raw fields.rAlpha0 fields.alpha1
    fields.rAlpha1 fields.alpha1Read
  exact ⟨hk,fields.alpha0,fields.alpha1,fields.alpha,h0,h1⟩
#print axioms resume_kappa_alpha_canonical
end AspisR1S9ResumeKappaAlphaCanonicalV1
