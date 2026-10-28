import R1Z.PV_B2_F_AuditCombined
import R1Z.PV_B2_F_FiveRows
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_AuditClosure
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier PV_B2_F_RawNative
abbrev E := ProverRwFull.aspis_core.field.wide_exact.WideExact

theorem closed_rows (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
    (ops : @ProverRwFull.ExternalFuns (types base)) (b : PV_B2_E_OrdinaryOriginal.Bytes)
    (w : W) (kappa : E) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) (kind j : Usize) :
    @ProverRwFull.ExternalFuns.op249 (types base) (selected base heap box ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_GammaOriginal.originalGamma b) ∧
    @ProverRwFull.ExternalFuns.op250 (types base) (selected base heap box ops) b =
      PV_B2_E_OrdinaryOriginal.mapResult PV_B2_E_OrdinaryOriginal.toNative
        (PV_B2_E_OrdinaryOriginal.original b) ∧
    @ProverRwFull.ExternalFuns.op251 (types base) (selected base heap box ops) w kappa =
      PV_B2_F_ResourceFamilies.heapOriginal heap w kappa ∧
    @ProverRwFull.ExternalFuns.op252 (types base) (selected base heap box ops) v alpha z =
      PV_B2_F_ResourceFamilies.boxOriginal box v alpha z ∧
    @ProverRwFull.ExternalFuns.op253 (types base) (selected base heap box ops) w kind j =
      originalCallback w kind j :=
  PV_B2_F_FiveRows.five_rows base heap box ops b w kappa v alpha z kind j

theorem nonvacuity (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (types base)) (b : PV_B2_E_OrdinaryOriginal.Bytes)
    (kappa : E) (v : NV) (alpha : Array NQ 10#usize) (z : Array NP 2#usize) :
    ∃ w : W, ∃ g o out q,
      @ProverRwFull.ExternalFuns.op249 (types base)
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) b = ok g ∧
      @ProverRwFull.ExternalFuns.op250 (types base)
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) b = ok o ∧
      @ProverRwFull.ExternalFuns.op251 (types base)
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) w kappa = ok (.Ok out) ∧
      @ProverRwFull.ExternalFuns.op252 (types base)
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) v alpha z = ok (.Ok w) ∧
      @ProverRwFull.ExternalFuns.op253 (types base)
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) w 0#usize 0#usize = ok q :=
  PV_B2_F_FiveRows.nonvacuity base ops b kappa v alpha z

#print axioms closed_rows
#print axioms nonvacuity
#print axioms PV_B2_E_GammaOriginal.copy_equal_original
#print axioms PV_B2_E_GammaOriginal.gamma_law
#print axioms PV_B2_E_GammaOriginal.nonvacuity
#print axioms PV_B2_E_OrdinaryOriginal.copy_equal_original
#print axioms PV_B2_E_Install250.value_law
#print axioms PV_B2_E_Install250.nonvacuity
#print axioms PV_B2_F_MaterializeRequest.complete_result
#print axioms PV_B2_F_ResourceFamilies.heap_source
#print axioms PV_B2_F_ResourceFamilies.box_source
#print axioms PV_B2_F_ConstructorEffect.value_law
#print axioms PV_B2_F_ConstructorCarrierLaws.weight_roundtrip
#print axioms PV_B2_F_RawNative.copy_equal_original
#print axioms PV_B2_F_RawNative.valid_value_law
#print axioms PV_B2_F_RawNative.dictionaries
#print axioms PV_B2_F_RawNative.observations
#print axioms PV_B2_F_RawNative.preserved_254
end PV_B2_F_AuditClosure
