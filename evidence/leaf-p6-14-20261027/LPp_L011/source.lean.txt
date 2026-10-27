import LPp_WrapperRawCircleSampleEmittedWrapperLaw
import ExtractedDigest32SamplerTransport
import AspisV8R19.SamplerClosureProductCorrectness

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualSamplerCanonicalV1

open AspisR1.ExtractedQM31SamplerCarrier
open AspisR1.ExtractedCurrentQM31Equality
open AspisR1.ExtractedCurrentQM31Exact
open AspisR1.ExtractedCurrentQM31Tower
open AspisR1.ExtractedCurrentTowerAdd
open AspisR1.ExtractedCurrentM31AddSub
open AspisR1PublicPreparation.SamplerTransport
open AspisV8R19.SamplerClosureProductCorrectness

/-- Canonicality of the actual wrapper sampler output follows from the
    existing byte-sampler proof, transported through the wrapper's explicit
    four-coordinate copy into the R72 representation. -/
theorem successful_sample_toR72_canonical
    (block : Array Std.U8 32#usize) (q : field.QM31)
    (h : sampler.qm31_sample block = ok q) :
    Canonical (toR72QM q) := by
  have heq := RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public block
  cases hp : AspisR1PublicPreparation.sampler.qm31_sample block with
  | ok qpub =>
      have hw : sampler.qm31_sample block = ok (fromPublicQM qpub) := by
        rw [heq, hp]
        rfl
      have hq : q = fromPublicQM qpub := Result.ok.inj (h.symm.trans hw)
      subst q
      obtain ⟨q0, h0, hc0, _⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total block
      have heq : qpub = q0 := Result.ok.inj (hp.symm.trans h0)
      subst qpub
      have hc := hc0
      change CanonicalCM (toCurrent (toOld q0)).c0 ∧
        CanonicalCM (toCurrent (toOld q0)).c1 at hc
      rcases hc with ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩
      change (toR72QM (fromPublicQM q0)).c0.a.val <
          AspisV8R15.ExactTowerBase.P ∧
        (toR72QM (fromPublicQM q0)).c0.b.val <
          AspisV8R15.ExactTowerBase.P ∧
        (toR72QM (fromPublicQM q0)).c1.a.val <
          AspisV8R15.ExactTowerBase.P ∧
        (toR72QM (fromPublicQM q0)).c1.b.val <
          AspisV8R15.ExactTowerBase.P
      simpa [toR72QM, toR72CM, fromPublicQM,
        AspisR1PublicPreparation.SamplerTransport.toOld, AspisR1.ExtractedQM31SamplerCarrier.toCurrent,
        AspisR1.ExtractedCurrentTowerAdd.CanonicalCM, AspisR1.ExtractedCurrentTowerAdd.CanonicalQM, AspisR1.ExtractedCurrentTowerAdd.P, AspisR1.ExtractedCurrentM31AddSub.P, AspisV8R15.ExactTowerBase.P] using
        And.intro h00 (And.intro h01 (And.intro h10 h11))
  | fail e =>
      simp only [heq, hp, bind_tc_fail] at h
      cases h
  | div =>
      simp only [heq, hp, bind_tc_div] at h
      cases h

#print axioms successful_sample_toR72_canonical
end RawCircleSampleActualSamplerCanonicalV1
end AspisR1CircleSampleWrapper
