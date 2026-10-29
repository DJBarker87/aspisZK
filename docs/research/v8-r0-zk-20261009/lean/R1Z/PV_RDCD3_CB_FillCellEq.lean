import R1Z.PV_RDCD3_CB_MaskExponentTables
import R1Z.PV_RDCD3_CB_MaskCell
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_FillCellEq
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
/-- Both index reads are known successful; only then is their order exchanged. -/
theorem cell {N : Usize} (data : Array Q N) (exponents : Array U8 N)
    (i : Usize) (coeff : Coeff) (inside : i.val<N.val) :
    PV_RDCD3_CB_OwnedMaskFill.step data (PV_RDCD3_CB_MaskExponentTables.widen exponents) i coeff =
      PV_RDCD3_CB_MaskCell.cell data exponents i coeff := by
  obtain ⟨e,he⟩ := PV_RDCD3_ArrayRead.read exponents i inside
  obtain ⟨q,hq⟩ := PV_RDCD3_ArrayRead.read data i inside
  simp only [PV_RDCD3_CB_OwnedMaskFill.step,PV_RDCD3_CB_MaskCell.cell,
    PV_RDCD3_CB_MaskExponentTables.read exponents i inside,he,hq,lift,bind_tc_ok,
    PV_RDCD3_CB_OwnedMaskLeaves.tower,PV_RDCD3_CB_OwnedMask.owned.cell]
#print axioms cell
end R1Z.PV_RDCD3_CB_FillCellEq
