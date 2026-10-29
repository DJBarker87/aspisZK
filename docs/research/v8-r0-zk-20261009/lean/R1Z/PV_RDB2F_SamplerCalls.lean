import R1Z.PV_RDB2F_Gamma
import R1Z.PV_RDB2F_Ordinary
import R1Z.PV_RDB2D_SamplerNative
namespace R1Z.PV_RDB2F_SamplerCalls
open Aeneas Aeneas.Std Result ProverRwFull PV_B2_E_OrdinaryOriginal PV_RDB2F_Iterator
set_option autoImplicit false
noncomputable section
/-- Exact inherited original callback, without editing its dictionary. The raw
Rust iterator/reference and deployed-caller associations are separate obligations. -/
theorem gamma_callback [ExternalTypes] (ops : ExternalFuns) (b : Bytes) :
    mapResult toNative (gamma b)=(PV_B2_E_GammaOriginal.selected ops).op249 b := by
  rw [gamma_complete]
  have h := PV_RDB2D_SamplerNative.gamma_callback ops b
  rw [PV_RDB2D_SamplerRestoration.gamma_complete] at h
  exact h

theorem ordinary_callback [ExternalTypes] (ops : ExternalFuns) (b : Bytes) :
    mapResult toNative (ordinary b)=(PV_B2_E_Install250.selected ops).op250 b := by
  rw [ordinary_complete]
  have h := PV_RDB2D_SamplerNative.ordinary_callback ops b
  rw [PV_RDB2D_SamplerRestoration.ordinary_complete] at h
  exact h

theorem gamma_caller [ExternalTypes] {A : Type} (ops : ExternalFuns)
    (b : Bytes) (caller : Native → Result A) :
    (mapResult toNative (gamma b) >>= caller)=
      ((PV_B2_E_GammaOriginal.selected ops).op249 b >>= caller) := by rw [gamma_callback]

theorem ordinary_caller [ExternalTypes] {A : Type} (ops : ExternalFuns)
    (b : Bytes) (caller : Native → Result A) :
    (mapResult toNative (ordinary b) >>= caller)=
      ((PV_B2_E_Install250.selected ops).op250 b >>= caller) := by rw [ordinary_callback]

#print axioms gamma_callback
#print axioms ordinary_callback
#print axioms gamma_caller
#print axioms ordinary_caller
end
end R1Z.PV_RDB2F_SamplerCalls
