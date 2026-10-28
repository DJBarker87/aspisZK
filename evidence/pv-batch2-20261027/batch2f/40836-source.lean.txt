import R1Z.PV_B2_F_MaterializeNative
import R1Z.PV_B2_F_MaterializeRequest
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_251Bridge
open Aeneas Aeneas.Std Result
open PV_B2_F_MaterializeNative
/-- Exact selected callback on the native carrier, full Result, every raw weight,
kappa, and allocation request result. This is not the native execution join. -/
theorem source (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base request ops) w kappa =
      PV_B2_E_OrdinaryOriginal.mapResult mapRust
        (PV_B2_F_MaterializeRequest.original request w (fromNative kappa)) := by
  change PV_B2_E_OrdinaryOriginal.mapResult mapRust
    (PV_B2_F_AllocationEffects.copied request w (fromNative kappa)) = _
  rw [PV_B2_F_MaterializeRequest.complete_result]

theorem nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    ∃ out, @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (ok .supplied) ops) w kappa = ok (.Ok out) :=
  PV_B2_F_MaterializeNative.nonvacuity base ops w kappa

theorem allocation_error (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (ok .denied) ops) w kappa = ok (.Err ProverRwFull.verifier.Error.Allocation) :=
  PV_B2_F_MaterializeNative.allocation_error base ops w kappa

theorem failure (base : ProverRwFull.ExternalTypes) (e : Error)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base (fail e) ops) w kappa = fail e := rfl

theorem divergence (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (w : W) (kappa : Native) :
    @ProverRwFull.ExternalFuns.op251 (types base)
      (selected base div ops) w kappa = div := rfl

theorem gamma_preserved (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op249 (types base) (selected base request ops) =
      @ProverRwFull.ExternalFuns.op249 (types base)
        (@PV_B2_E_GammaOriginal.selected (types base) ops) := rfl

theorem ordinary_preserved (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (ops : @ProverRwFull.ExternalFuns (types base)) :
    @ProverRwFull.ExternalFuns.op250 (types base) (selected base request ops) =
      @ProverRwFull.ExternalFuns.op250 (types base)
        (@PV_B2_E_GammaOriginal.selected (types base) ops) := rfl
#print axioms source
#print axioms nonvacuity
#print axioms allocation_error
#print axioms failure
#print axioms divergence
#print axioms gamma_preserved
#print axioms ordinary_preserved
end PV_B2_F_251Bridge
