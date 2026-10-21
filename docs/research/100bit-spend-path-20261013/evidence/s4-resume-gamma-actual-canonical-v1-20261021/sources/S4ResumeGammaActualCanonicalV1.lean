import OraclePortCkptAbiSourceFields
import S4ReaderEActualWideCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4ResumeGammaActualCanonicalV1

open AspisR1Stage2
open AspisR1.OraclePortCkptAbiSourceFields
open AspisR1S4ReaderEActualWideCanonicalV1

/-- Install the exact Reader.e source cut into the resume model. The raw
reader remains the caller-supplied source operation; the decoder and
noncanonical rejection are fixed by the checked source cut. -/
def withReaderE (ops : ResumeOps) : ResumeOps :=
  { ops with readE := readerE ops.raw }

/-- On the same successful resume call, the gamma stored in Prepared is the
value returned by its first E read. The concrete Reader.e decoder then gives
all eight canonical limb bounds without an independent canonicality premise. -/
theorem resume_gamma_canonical
    (ops : ResumeOps) {H : Type}
    (digestInst : aspis_core.digest.Digest32 H)
    (bytes proof public1 : Slice Std.U8) (v : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (success : verifier.resumeWithOps (withReaderE ops) digestInst
      bytes proof public1 v hash = ok (.Ok (p,acc))) :
    currentWideCanonical p.gamma := by
  obtain ⟨fields⟩ := successful_fields (withReaderE ops) digestInst
    bytes proof public1 v hash p acc success
  exact readerE_success_canonical ops.raw fields.rRoot1 p.gamma
    fields.rGamma fields.gammaRead

#print axioms resume_gamma_canonical

end AspisR1S4ResumeGammaActualCanonicalV1
