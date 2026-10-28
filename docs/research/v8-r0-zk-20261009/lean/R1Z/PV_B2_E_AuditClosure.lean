import R1Z.PV_B2_E_AuditCombined
import R1Z.PV_B2_E_GammaOriginal
import R1Z.PV_B2_E_AuditCtDecoder
set_option autoImplicit false
noncomputable section
namespace PV_B2_E_AuditClosure
open Aeneas Aeneas.Std Result ProverRwFull PV_B2_E_OrdinaryOriginal
variable [ExternalTypes]
/-- Focused two-row composition, retaining every other callback in the supplied
carrier. This is not the deployed privacy endpoint or a physical observer law. -/
theorem sampler_rows (ops : ExternalFuns) (b : Bytes) :
    (PV_B2_E_GammaOriginal.selected ops).op249 b =
      mapResult toNative (PV_B2_E_GammaOriginal.originalGamma b) ∧
    (PV_B2_E_GammaOriginal.selected ops).op250 b =
      mapResult toNative (original b) :=
  ⟨PV_B2_E_GammaOriginal.selected_callback ops b,
   PV_B2_E_Install250.selected_callback ops b⟩

theorem dictionary_observations {O : Sort _} (observe : ExternalFuns → O)
    (ops : ExternalFuns) :
    observe (PV_B2_E_GammaOriginal.selected ops) =
      observe (PV_B2_E_GammaOriginal.originalDictionary ops) :=
  PV_B2_E_GammaOriginal.observations observe ops
#print axioms PV_B2_E_AuditCtDecoder.source_canonical
#print axioms sampler_rows
#print axioms dictionary_observations
#print axioms PV_B2_E_Install250.value_law
#print axioms PV_B2_E_Install250.nonvacuity
#print axioms PV_B2_E_GammaOriginal.gamma_law
#print axioms PV_B2_E_GammaOriginal.nonvacuity
#print axioms PV_B2_D_MaterializeTotal.source
#print axioms PV_B2_C_ConstructorSuccess.new_total
#print axioms PV_B2_C_ConstructorSuccess.new_eq_staged
end PV_B2_E_AuditClosure
