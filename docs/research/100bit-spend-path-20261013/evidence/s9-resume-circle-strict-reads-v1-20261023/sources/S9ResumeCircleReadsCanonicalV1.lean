import OraclePortCkptAbiSourceFields
import S9ReaderKActualQMCanonicalV1
import S4ResumeGammaActualCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeCircleReadsCanonicalV1
open AspisR1Stage2
open AspisR1S9ReaderKActualQMCanonicalV1

def withReaderK (ops : ResumeOps) : ResumeOps := {ops with readK := readerK ops.raw}
def withStrictReaders (ops : ResumeOps) : ResumeOps :=
  withReaderK (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE ops)

/-- The same successful resume supplies four canonical coordinates for its
stored circle input. These come from strict checkpoint reads, independently
of the circle sampler's distribution or inverse-map algebra. The raw reader
and source/callee refinement are still explicit boundaries. -/
theorem resume_success_circle_coordinates_canonical
    (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (variant : transport.Variant) (hash : H)
    (p : verifier.Prepared) (acc : verifier.Accumulator)
    (h : verifier.resumeWithOps (withReaderK ops) D bytes proof publicInput variant hash = .ok (.Ok (p,acc))) :
    ∃ (x0 y0 x1 y1 : K),
      p.z = Array.make 2#usize [⟨x0,y0⟩,⟨x1,y1⟩] ∧
      Canonical x0 ∧ Canonical y0 ∧ Canonical x1 ∧ Canonical y1 := by
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (withReaderK ops) D bytes proof publicInput variant hash p acc h
  refine ⟨fields.x0,fields.y0,fields.x1,fields.y1,fields.coordinates,?_,?_,?_,?_⟩
  · exact readerK_success_canonical ops.raw _ _ _ fields.x0Read
  · exact readerK_success_canonical ops.raw _ _ _ fields.y0Read
  · exact readerK_success_canonical ops.raw _ _ _ fields.x1Read
  · exact readerK_success_canonical ops.raw _ _ _ fields.y1Read

#print axioms resume_success_circle_coordinates_canonical
end AspisR1S9ResumeCircleReadsCanonicalV1
