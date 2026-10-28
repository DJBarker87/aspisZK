import R1Z.PV_B2_F_RawNative
set_option autoImplicit false
noncomputable section
namespace PV_B2_F_FiveRows
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier PV_B2_F_RawNative
abbrev E := ProverRwFull.aspis_core.field.wide_exact.WideExact

theorem five_rows (base : ProverRwFull.ExternalTypes) (heap : HeapRequest) (box : BoxRequest)
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
      originalCallback w kind j := by
  refine ⟨?_,?_,?_,?_,PV_B2_F_RawNative.source base heap box ops w kind j⟩
  · change @ProverRwFull.ExternalFuns.op249 (types base)
      (@PV_B2_E_GammaOriginal.selected (types base) ops) b = _
    exact @PV_B2_E_GammaOriginal.selected_callback (types base) ops b
  · change @ProverRwFull.ExternalFuns.op250 (types base)
      (@PV_B2_E_Install250.selected (types base) ops) b = _
    exact @PV_B2_E_Install250.selected_callback (types base) ops b
  · exact PV_B2_F_ResourceFamilies.selected_heap base heap box ops w kappa
  · exact PV_B2_F_ResourceFamilies.selected_box base heap box ops v alpha z

/-- One complete success-context path shares the actual constructed weights
between op252, op251 and op253; its existence does not assume native success. -/
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
        (selected base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops) w 0#usize 0#usize = ok q := by
  obtain ⟨c,_,hc⟩ := PV_B2_F_ConstructorEffect.value_law v alpha z
  obtain ⟨g,hg⟩ := @PV_B2_E_GammaOriginal.nonfailure (types base) ops b
  obtain ⟨o,ho⟩ := @PV_B2_E_Install250.nonfailure (types base) ops b
  obtain ⟨out,hm⟩ := PV_B2_F_ResourceFamilies.heap_nonvacuity base ops (toWeight c) kappa
  obtain ⟨q,hq⟩ := PV_B2_F_RawNative.nonvacuity base (fun _ _ => ok .supplied) (fun _ _ _ => ok ()) ops (toWeight c)
  exact ⟨toWeight c,g,o,out,q,hg,ho,hm,hc,hq⟩
#print axioms five_rows
#print axioms nonvacuity
#print axioms PV_B2_F_RawNative.copy_equal_original
#print axioms PV_B2_F_RawNative.source
#print axioms PV_B2_F_RawNative.valid_value_law
#print axioms PV_B2_F_RawNative.nonvacuity
#print axioms PV_B2_F_RawNative.dictionaries
#print axioms PV_B2_F_RawNative.observations
#print axioms PV_B2_F_ResourceFamilies.heap_source
#print axioms PV_B2_F_ResourceFamilies.box_source
end PV_B2_F_FiveRows
