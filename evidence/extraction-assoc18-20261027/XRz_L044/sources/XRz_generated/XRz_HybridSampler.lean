import XRq_GammaScalar
import LPk_Result
open Aeneas Aeneas.Std Result XRn_Join_Release XRo_Join_Carriers
set_option autoImplicit false
namespace XRz_HybridSampler
/-- Only the excluded leaf is replaced. The outer continuations remain emitted. -/
abbrev Low := XRq_SamplerInterface.Low
abbrev adopted : Low := AspisR1Post25Sampler.sampler.low_base_p_digits
abbrev scalar := @XRq_OrdinaryScalar.scalar
/-- This is the CLOSED LPk leaf's cohort endpoint, not the refuted emitted law. -/
theorem ordinary {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (p.1,ct p.2)) (scalar adopted (ed D) (et t) row payload false)=
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling D t row payload false :=
 XRq_OrdinaryScalar.ordinary D t row payload
/-- The remaining add-continuation association is explicit and OPEN. -/
theorem gamma (add : XRq_GammaAssociation.AddAssociation)
 {H : Type} (D : C.D H) (t : C.T H) (row : U8) (payload : Slice U8) :
 mapR (fun p => (p.1,ct p.2)) (scalar adopted (ed D) (et t) row payload true)=
 AspisR1PublicPreparation.PreparedModel.scalar XRo_Join_Installed.actual.sampling D t row payload true :=
 XRq_GammaScalar.source add D t row payload
#print axioms LPk_Result.native_result
#print axioms ordinary
#print axioms gamma
end XRz_HybridSampler
