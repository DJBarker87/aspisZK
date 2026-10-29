import R1Z.PV_RDB2D_GammaRestoration
import R1Z.PV_RDB2D_OrdinaryRestoration
import R1Z.PV_RDB2D_GammaOriginal
namespace R1Z.PV_RDB2D_SamplerNative
open Aeneas Aeneas.Std Result ProverRwFull PV_B2_E_OrdinaryOriginal
open PV_RDB2D_SamplerRestoration
set_option autoImplicit false
noncomputable section

/-- Exact original native carrier/callback projection of the restoration model.
This theorem does not assert the remaining native iterator source association. -/
theorem gamma_callback [ExternalTypes] (ops : ExternalFuns) (b : Bytes) :
    mapResult toNative (gamma b)=(PV_B2_E_GammaOriginal.selected ops).op249 b := by
  change mapResult toNative (gamma b)=
    mapResult toNative (PV_B2_C_249.host_sampler.gamma_sample b)
  rw [gamma_complete,PV_B2_C_GammaSource.raw_eq]

theorem ordinary_callback [ExternalTypes] (ops : ExternalFuns) (b : Bytes) :
    mapResult toNative (ordinary b)=(PV_B2_E_Install250.selected ops).op250 b := by
  change mapResult toNative (ordinary b)=
    mapResult toNative (PV_B2_C_Sampler.host_sampler.ordinary_sample b)
  rw [ordinary_complete]

theorem all_eight_fields (v : Raw) : fromNative (toNative v)=v := roundtrip v

theorem gamma_with_caller [ExternalTypes] {A : Type}
    (ops : ExternalFuns) (b : Bytes) (caller : Native → Result A) :
    (mapResult toNative (gamma b) >>= caller)=
      ((PV_B2_E_GammaOriginal.selected ops).op249 b >>= caller) := by rw [gamma_callback]

theorem ordinary_with_caller [ExternalTypes] {A : Type}
    (ops : ExternalFuns) (b : Bytes) (caller : Native → Result A) :
    (mapResult toNative (ordinary b) >>= caller)=
      ((PV_B2_E_Install250.selected ops).op250 b >>= caller) := by rw [ordinary_callback]

#print axioms gamma_callback
#print axioms ordinary_callback
#print axioms all_eight_fields
#print axioms gamma_with_caller
#print axioms ordinary_with_caller
end
end R1Z.PV_RDB2D_SamplerNative
