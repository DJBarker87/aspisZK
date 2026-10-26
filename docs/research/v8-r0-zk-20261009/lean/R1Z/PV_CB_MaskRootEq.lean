import R1Z.PV_CB_FillLoopsEq
import R1Z.PV_CB_OwnedMaskLinearsEq
import R1Z.PV_CB_OwnedMaskHornerEq
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskRootEq
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
/-- Prepared control equality only. The fresh shipped/P6 association is separate. -/
theorem reference (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) :
    PV_CB_OwnedMask.owned.mask c1 mask g point =
      PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value c1 mask g point := by
  simp only [PV_CB_OwnedMask.owned.mask,
    PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value,
    PV_CB_OwnedMaskLinearsEq.source,PV_CB_FillLoopsEq.c1,PV_CB_FillLoopsEq.mask,
    PV_CB_OwnedMaskHornerEq.source,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    PV_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE,
    core.iter.traits.iterator.Iterator.rev.default,
    core.iter.traits.iterator.Iterator.rev.trait_default,
    bind_tc_ok,bind_assoc_eq,PV_CB_MaskHorner.S.loop,PV_CB_MaskSource.state_only_hiding.mask_power_26,
    ProverRwSuccessReverseRange.before,PV_CB_ForwardRange.between]
#print axioms reference
end R1Z.PV_CB_MaskRootEq
