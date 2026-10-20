import Stage2ResumeFixedReadPrefix
import Stage2ResumeConcreteDecoderCanonicality

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.PrefixCanonicalOutputs

open AspisR1Stage2AdoptedReader
open AspisR1Stage2AdoptedReader.ResumeFixedPrefix
open AspisR1Stage2AdoptedReader.ConcreteDecoderCanonicality

/-- With the concrete QM31 and WideExact parsers installed, any successful
    fixed-prefix read yields canonical gamma, kappa, alpha₀, alpha₁, and rho.
    The array unwrap adapter is intentionally arbitrary: canonicality follows
    from the concrete decoders' successful-result contracts, not byte identity. -/
theorem successful_prefix_outputs_canonical
    (unwrap : {n : Usize} →
      core.result.Result (Array Std.U8 n) core.array.TryFromSliceError →
      Result (Array Std.U8 n))
    (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : ReaderWide) (rho : ReaderQM)
    (rfinal : verifier.Reader)
    (h : readPrefix (actualReaderDecoders unwrap) bytes = ok
      ((state, root0, root1, .Ok gamma, .Ok kappa, .Ok alpha0, .Ok alpha1, .Ok rho), rfinal)) :
    readerWideCanonical gamma ∧ readerWideCanonical kappa ∧
      readerWideCanonical alpha0 ∧ readerWideCanonical alpha1 ∧ readerQMCanonical rho := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ⟨rawGamma, _, hGamma⟩,
    ⟨rawKappa, _, hKappa⟩,
    ⟨rawAlpha0, _, hAlpha0⟩,
    ⟨rawAlpha1, _, hAlpha1⟩,
    ⟨rawRho, _, hRho⟩⟩ := successful_prefix_decodes
      (actualReaderDecoders unwrap) bytes state root0 root1 gamma kappa alpha0 alpha1 rho rfinal h
  change actualWideDecoder rawGamma.to_slice = .ok (some gamma) at hGamma
  change actualWideDecoder rawKappa.to_slice = .ok (some kappa) at hKappa
  change actualWideDecoder rawAlpha0.to_slice = .ok (some alpha0) at hAlpha0
  change actualWideDecoder rawAlpha1.to_slice = .ok (some alpha1) at hAlpha1
  change actualQMDecoder rawRho.to_slice = .ok (some rho) at hRho
  exact ⟨actualWideDecoder_success_canonical _ _ hGamma,
    actualWideDecoder_success_canonical _ _ hKappa,
    actualWideDecoder_success_canonical _ _ hAlpha0,
    actualWideDecoder_success_canonical _ _ hAlpha1,
    actualQMDecoder_success_canonical _ _ hRho⟩

#print axioms successful_prefix_outputs_canonical

end AspisR1Stage2AdoptedReader.PrefixCanonicalOutputs
