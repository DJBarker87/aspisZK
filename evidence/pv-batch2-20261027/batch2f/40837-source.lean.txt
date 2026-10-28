import R1Z.PV_B2_E_AuditFinal
import R1Z.PV_B2_F_251Bridge
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_251Closure
open Aeneas Aeneas.Std Result PV_B2_F_MaterializeNative

theorem three_rows (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base))
    (b : PV_B2_E_OrdinaryOriginal.Bytes) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op249 (types base) (selected base request ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_GammaOriginal.originalGamma b) ∧
    @ProverRwFull.ExternalFuns.op250 (types base) (selected base request ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_OrdinaryOriginal.original b) ∧
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base request ops) w kappa =
      PV_B2_E_OrdinaryOriginal.mapResult mapRust
        (PV_B2_F_MaterializeRequest.original request w (fromNative kappa)) := by
  refine ⟨?_,?_,PV_B2_F_251Bridge.source base request ops w kappa⟩
  · change @ProverRwFull.ExternalFuns.op249 (types base)
      (@PV_B2_E_GammaOriginal.selected (types base) ops) b = _
    exact @PV_B2_E_GammaOriginal.selected_callback (types base) ops b
  · change @ProverRwFull.ExternalFuns.op250 (types base)
      (@PV_B2_E_Install250.selected (types base) ops) b = _
    exact @PV_B2_E_Install250.selected_callback (types base) ops b

#print axioms three_rows
#print axioms PV_B2_F_MaterializeRequest.complete_result
#print axioms PV_B2_F_251Bridge.source
#print axioms PV_B2_F_251Bridge.nonvacuity
#print axioms PV_B2_F_251Bridge.allocation_error
#print axioms PV_B2_F_251Bridge.failure
#print axioms PV_B2_F_251Bridge.divergence
#print axioms PV_B2_F_MaterializeNative.dictionaries
#print axioms PV_B2_F_MaterializeNative.observations
#print axioms PV_B2_E_GammaOriginal.copy_equal_original
#print axioms PV_B2_E_GammaOriginal.gamma_law
#print axioms PV_B2_E_GammaOriginal.nonvacuity
#print axioms PV_B2_E_OrdinaryOriginal.copy_equal_original
#print axioms PV_B2_E_Install250.value_law
#print axioms PV_B2_E_Install250.nonvacuity
end PV_B2_F_251Closure
