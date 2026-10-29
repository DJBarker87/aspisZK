import R1Z.PV_RDCD3_V217
import R1Z.PV_RDCD3_V217FillTotal
import R1Z.PV_RDCD3_V217ReverseTotal
import R1Z.PV_RDCD3_V217HornerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_V217Total
open Aeneas Aeneas.Std Result PV_RDCD3_Total
abbrev Q := ProverRwFull.aspis_core.field.QM31
namespace S
abbrev source := PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value
end S
/-- Every typed input succeeds in the source-shaped Result model. Primitive
compiler/runtime fidelity and the physical observer remain explicitly retained. -/
theorem complete (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) : Total (S.source c1 mask g point) := by
  unfold S.source PV_RDCD3_CB_MaskSource.state_only_hiding.state_only_selected_mask_value
  simp only [PV_RDCD3_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS,
    PV_RDCD3_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS,
    PV_RDCD3_CB_MaskSource.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE,
    core.iter.traits.iterator.Iterator.rev.default,
    core.iter.traits.iterator.Iterator.rev.trait_default,bind_tc_ok]
  apply bind_total (PV_RDCD3_V217ReverseTotal.complete point)
  rintro ⟨linear,explicit⟩
  apply bind_total (PV_RDCD3_V217FillTotal.c1 c1 _);intro coeff
  apply bind_total (PV_RDCD3_V217FillTotal.mask mask coeff);intro coeff1
  apply bind_total (PV_RDCD3_CB_PreparedTotal.new linear);intro prepared
  apply bind_total (PV_RDCD3_ArrayRead.read coeff1 26#usize (by decide));intro shared
  apply bind_total (PV_RDCD3_V217HornerTotal.source_total coeff1 prepared shared);intro shared1
  apply bind_total (PV_RDCD3_CB_MaskLeaves.power explicit);intro power
  apply bind_total (PV_RDCD3_FieldTotal.q_add _ power);intro factor
  apply bind_total (PV_RDCD3_FieldTotal.q_mul factor g);intro term
  exact PV_RDCD3_FieldTotal.q_add shared1 term

theorem owned (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) :
    Total (PV_RDCD3_CB_OwnedMask.owned.mask c1 mask g point) := by
  rw [←PV_RDCD3_V217.complete]
  exact complete c1 mask g point
#print axioms complete
#print axioms owned
end R1Z.PV_RDCD3_V217Total
