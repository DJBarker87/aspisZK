import XRq_Audit
import XRs_AddAssociation
import XRs_Serializer
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
noncomputable section
namespace XRs_ClosedCallbacks

theorem add : XRq_GammaAssociation.AddAssociation := XRs_AddAssociation.add

theorem scalar (low : XRq_SamplerInterface.Low)
 (leaf : ∀ b, low b = AspisR1Post25Sampler.sampler.low_base_p_digits b)
 {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) (nonzero : Bool) :
 mapR (fun p => (p.1,ct p.2))
  (XRq_OrdinaryScalar.scalar low (ed D) (et t) row payload nonzero) =
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling
  D t row payload nonzero := by
 have hl : low = AspisR1Post25Sampler.sampler.low_base_p_digits := funext leaf
 rw [hl]
 cases nonzero with
 | false => exact XRq_OrdinaryScalar.ordinary D t row payload
 | true => exact XRq_GammaScalar.source add D t row payload

theorem serializer (x : C.E) :
 aspis_core.field.wide_exact.WideExact.to_le_bytes x =
 XRo_Join_Installed.actual.sampling.toBytes x := XRs_Serializer.same_eight_limbs x

#print axioms add
#print axioms scalar
#print axioms serializer
end XRs_ClosedCallbacks
end
