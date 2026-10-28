import R1Z.PV_B2_F_251Closure
import R1Z.PV_B2_F_ConstructorNative
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_252Closure
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier PV_B2_F_ConstructorNative
abbrev E := ProverRwFull.aspis_core.field.wide_exact.WideExact

theorem four_rows (base : ProverRwFull.ExternalTypes) (request : Result Outcome)
    (boxRequest : Result Unit) (ops : @ProverRwFull.ExternalFuns (types base))
    (b : PV_B2_E_OrdinaryOriginal.Bytes) (w : W) (kappa : E)
    (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    @ProverRwFull.ExternalFuns.op249 (types base) (selected base request boxRequest ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_GammaOriginal.originalGamma b) ∧
    @ProverRwFull.ExternalFuns.op250 (types base) (selected base request boxRequest ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_OrdinaryOriginal.original b) ∧
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base request boxRequest ops) w kappa =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_F_MaterializeNative.mapRust
        (PV_B2_F_MaterializeRequest.original request w (PV_B2_F_MaterializeNative.fromNative kappa)) ∧
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base request boxRequest ops) v alpha z =
      PV_B2_F_ConstructorEffect.original boxRequest v alpha z := by
  obtain ⟨h249,h250,h251⟩ := PV_B2_F_251Closure.three_rows base request ops b w kappa
  exact ⟨h249,h250,h251,PV_B2_F_ConstructorNative.source base request boxRequest ops v alpha z⟩
#print axioms four_rows
#print axioms PV_B2_F_ConstructorEffect.complete_result
#print axioms PV_B2_F_ConstructorNative.source
#print axioms PV_B2_F_ConstructorNative.value_law
#print axioms PV_B2_F_ConstructorNative.nonvacuity
#print axioms PV_B2_F_ConstructorNative.failure
#print axioms PV_B2_F_ConstructorNative.divergence
#print axioms PV_B2_F_ConstructorNative.dictionaries
#print axioms PV_B2_F_ConstructorNative.observations
end PV_B2_F_252Closure
