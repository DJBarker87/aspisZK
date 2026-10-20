import Stage2GeneratedPrefixCallCanonicality
import CurrentFinishArithmetic

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FinishPrefixAlphaCanonicalityV1

abbrev GenWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev ReaderWide := AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderWide
abbrev FinishE := AspisR1CurrentWide.Proof.FinishE

def generatedWideToReader (w : GenWide) : ReaderWide :=
  ⟨⟨⟨w.c0.c0.a, w.c0.c0.b⟩, ⟨w.c0.c1.a, w.c0.c1.b⟩⟩,
    ⟨⟨w.c1.c0.a, w.c1.c0.b⟩, ⟨w.c1.c1.a, w.c1.c1.b⟩⟩⟩

def generatedWideToFinish (w : GenWide) : FinishE :=
  ⟨⟨⟨⟨w.c0.c0.a, w.c0.c0.b⟩, ⟨w.c0.c1.a, w.c0.c1.b⟩⟩,
      ⟨⟨w.c1.c0.a, w.c1.c0.b⟩, ⟨w.c1.c1.a, w.c1.c1.b⟩⟩⟩⟩

theorem generated_wide_canonical_to_finish (w : GenWide)
    (h : AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (generatedWideToReader w)) :
    AspisR1CurrentWide.Proof.CanonicalFinish (generatedWideToFinish w) := by
  simpa [AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical,
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerQMCanonical,
    AspisR1CurrentWide.Proof.CanonicalFinish,
    AspisR1CurrentWide.Proof.CanonicalWide,
    AspisR1CurrentWide.Proof.CanonicalQM,
    AspisR1CurrentWide.Proof.ofFinishE,
    AspisR1CurrentWide.Proof.ofFinishQM,
    AspisR1CurrentWide.Proof.ofFinishCM,
    AspisR1CurrentWide.Proof.toQM,
    AspisR1CurrentWide.Proof.toCM,
    AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
    AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
    AspisR1.ExtractedCurrentM31AddSub.P] using h

theorem successful_prefix_alpha_canonical_to_finish
    (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : GenWide)
    (rho : AspisR1Stage2AdoptedResume.aspis_core.field.QM31)
    (finalAt : Usize)
    (h : AspisR1Stage2AdoptedResume.verifier.resume_read_prefix bytes =
      ok (.Ok (state, Array.make 2#usize [root0, root1], gamma, kappa,
        Array.make 2#usize [alpha0, alpha1], rho, finalAt))) :
    AspisR1CurrentWide.Proof.CanonicalFinish (generatedWideToFinish alpha0) ∧
      AspisR1CurrentWide.Proof.CanonicalFinish (generatedWideToFinish alpha1) := by
  obtain ⟨hgamma, hkappa, halpha0, halpha1, _hrho⟩ :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality
      .successful_generated_prefix_outputs_canonical
        bytes state root0 root1 gamma kappa alpha0 alpha1 rho finalAt h
  exact ⟨generated_wide_canonical_to_finish alpha0 halpha0,
    generated_wide_canonical_to_finish alpha1 halpha1⟩

#print axioms generated_wide_canonical_to_finish
#print axioms successful_prefix_alpha_canonical_to_finish

end AspisR1FinishPrefixAlphaCanonicalityV1
