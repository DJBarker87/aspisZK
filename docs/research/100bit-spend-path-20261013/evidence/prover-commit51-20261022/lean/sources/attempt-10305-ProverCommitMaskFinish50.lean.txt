import AspisR1ProducerRelease47.MaskFinish50
import R1Z.ProverCommitLinear50
import R1Z.ProverCommitSampleTail49
/-! Actual selected-mask final arithmetic, after the shared Horner result.
The shared coefficient-producer provenance remains an independent obligation. -/
set_option autoImplicit false
namespace R1Z.ProverCommitMaskFinish50
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitSubtraction47 (one one_canonical one_decode)

theorem exact_result (shared x g : Old.Q) (hs : Canonical shared) (hx : Canonical x) (hg : Canonical g) :
    ∃ z : Old.Q, mask_finish50.eval (ProverCommitNativeQ48.source shared) (ProverCommitNativeQ48.source x)
      (ProverCommitNativeQ48.source g)=ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=decode shared+(1+(decode x)^26)*decode g := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitLinear50.power26 x hx
  obtain ⟨factor,hfactor,hcfactor,hdfactor⟩ := ProverCommitNativeQ48.add one p one_canonical hcp
  obtain ⟨extra,hextra,hcextra,hdextra⟩ := ProverCommitNativeQ48.mul factor g hcfactor hg
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitNativeQ48.add shared extra hs hcextra
  refine ⟨z,?_,hcz,?_⟩
  · simp only [mask_finish50.eval,hp,ProverCommitSampleTail49.source_one,hfactor,hextra,hz,bind_tc_ok]
  · rw [hdz,hdextra,hdfactor,one_decode,hdp]

#print axioms exact_result
end R1Z.ProverCommitMaskFinish50
