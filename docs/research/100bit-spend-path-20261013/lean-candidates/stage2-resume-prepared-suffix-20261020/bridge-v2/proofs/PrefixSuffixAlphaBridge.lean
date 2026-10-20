import Stage2GeneratedPrefixCallCanonicality
import SuffixPreparedFields

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2ResumePrefixSuffixBridge

abbrev GenWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev GenQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31
abbrev SufWide := AspisR1Stage2ResumeSuffix.aspis_core.field.WideExact
abbrev SufQM := AspisR1Stage2ResumeSuffix.aspis_core.field.QM31

def genCMToSuffix (x : AspisR1Stage2AdoptedResume.aspis_core.field.CM31) :
    AspisR1Stage2ResumeSuffix.aspis_core.field.CM31 :=
  ⟨x.a, x.b⟩

def genQMToSuffix (x : GenQM) : SufQM :=
  ⟨genCMToSuffix x.c0, genCMToSuffix x.c1⟩

def genWideToSuffix (x : GenWide) : SufWide :=
  ⟨genQMToSuffix x.c0, genQMToSuffix x.c1⟩

def genQMToReader (x : GenQM) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def genWideToReader (x : GenWide) :
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.ReaderWide :=
  ⟨genQMToReader x.c0, genQMToReader x.c1⟩

theorem successful_prefix_and_suffix_prepared_alpha
    (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : GenWide) (rho : GenQM) (finalAt : Usize)
    (hprefix : AspisR1Stage2AdoptedResume.verifier.resume_read_prefix bytes =
      ok (.Ok (state, Array.make 2#usize [root0, root1], gamma, kappa,
        Array.make 2#usize [alpha0, alpha1], rho, finalAt)))
    (v : AspisR1Stage2ResumeSuffix.transport.Variant)
    (roots : Array (Array Std.U8 32#usize) 2#usize)
    (gamma' kappa' : SufWide)
    (rho' : SufQM)
    (queries : Array Std.U32 22#usize)
    (semanticAlpha : Array SufQM 10#usize)
    (z : Array AspisR1Stage2ResumeSuffix.aspis_core.circle.SecureCirclePoint 2#usize)
    (claim : SufWide) (suffixState : Array Std.U8 32#usize)
    (weights : alloc.vec.Vec SufQM) (rhs : SufWide) (power : SufQM)
    (p : AspisR1Stage2ResumeSuffix.verifier.Prepared)
    (a : AspisR1Stage2ResumeSuffix.verifier.Accumulator)
    (hsuffix : AspisR1Stage2ResumeSuffix.verifier.resume_prepared_suffix bytes v roots gamma' kappa'
      (Array.make 2#usize [genWideToSuffix alpha0, genWideToSuffix alpha1])
      rho' queries semanticAlpha z claim suffixState weights rhs power =
        .ok (.Ok (p, a))) :
    p.alpha = Array.make 2#usize [genWideToSuffix alpha0, genWideToSuffix alpha1] ∧
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (genWideToReader alpha0) ∧
    AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality.readerWideCanonical
      (genWideToReader alpha1) := by
  have hcanonical :=
    AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality.successful_generated_prefix_outputs_canonical
      bytes state root0 root1 gamma kappa alpha0 alpha1 rho finalAt hprefix
  have halpha0 := hcanonical.2.2.1
  have halpha1 := hcanonical.2.2.2.1
  have hprepared :=
    AspisR1Stage2ResumeSuffix.successful_suffix_prepared_eq bytes v roots gamma' kappa'
      (Array.make 2#usize [genWideToSuffix alpha0, genWideToSuffix alpha1])
      rho' queries semanticAlpha z claim suffixState weights rhs power p a hsuffix
  have hmap0 : genWideToReader alpha0 =
      AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality.genWideToRead alpha0 := rfl
  have hmap1 : genWideToReader alpha1 =
      AspisR1Stage2AdoptedReader.GeneratedPrefixCallCanonicality.genWideToRead alpha1 := rfl
  exact ⟨by rw [hprepared], hmap0 ▸ halpha0, hmap1 ▸ halpha1⟩

#print axioms successful_prefix_and_suffix_prepared_alpha

end AspisR1Stage2ResumePrefixSuffixBridge
