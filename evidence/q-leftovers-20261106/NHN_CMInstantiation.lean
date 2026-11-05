import NHH_CMAll
import NHH_CMBridge
import NHH_InverseOutcomes
set_option autoImplicit false
noncomputable section
namespace NHN_CMInstantiation
open Aeneas Aeneas.Std Result
open NHH_CMInverse (C Canon toSampler)

/-- The deployed instantiation is the actual fixed M31 backend on the SAME
norm, preserving the complete partial Result on every raw receiver. -/
theorem association (x : C) :
 (do let out ← NFG_InverseRef.field.CM31.inv_with x NFG_InverseRef.field.M31.inv
     ok (toSampler out))=
 AspisR72Sampler.field.CM31.inv_with (toSampler x) AspisR72Sampler.field.M31.inv := by
 rw [show NFG_InverseRef.field.M31.inv=AspisR72Sampler.field.M31.inv from
  funext NHH_AllScalar.inverse]
 exact NHH_CMAll.inv_with x _

theorem packet (x : C) (hx : Canon x) (hl : NHH_CMBridge.Live x) :
 ∃ out,
 NHH_CMTrace.run x=ok (out,NHH_CMTrace.log (NHH_CMInverse.decode x)) ∧ Canon out ∧
 NFG_InverseRef.field.CM31.inv_with x NFG_InverseRef.field.M31.inv=ok out ∧
 AspisR72Sampler.field.CM31.inv_with (toSampler x) AspisR72Sampler.field.M31.inv=
  ok (toSampler out) := by
 obtain ⟨out,ht,hc,hs,hm⟩ := NHH_CMBridge.packet x hx hl
 exact ⟨out,ht,hc,hs,hm⟩

/-- Zero reaches precisely the retained native assertion failure. A successful
backend reply is never assumed as a premise. -/
theorem outcomes (x : C) (hx : Canon x) :
 NFG_InverseRef.field.CM31.inv_with x NFG_InverseRef.field.M31.inv=
 if NHH_CMInverse.decode x=0 then fail .assertionFailure
 else ok (NHH_CMInverse.encode (NHH_CMInverse.decode x)⁻¹) :=
 NHH_InverseOutcomes.complex x hx

#print axioms association
#print axioms packet
#print axioms outcomes
end NHN_CMInstantiation
end
