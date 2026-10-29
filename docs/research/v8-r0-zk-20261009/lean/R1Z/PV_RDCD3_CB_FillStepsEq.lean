import R1Z.PV_RDCD3_CB_FillCellEq
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_FillStepsEq
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Coeff := Array Q 27#usize
theorem c1 (data : Array Q 16#usize) (i : Usize) (coeff : Coeff) (inside : i.val<16) :
    PV_RDCD3_CB_OwnedMaskFill.step data PV_RDCD3_CB_OwnedMaskFill.c1Exponents i coeff =
      PV_RDCD3_CB_MaskCell.cell data PV_RDCD3_CB_MaskIndices.S.factors i coeff := by
  rw [PV_RDCD3_CB_MaskExponentTables.c1]
  exact PV_RDCD3_CB_FillCellEq.cell data _ i coeff inside
theorem mask (data : Array Q 10#usize) (i : Usize) (coeff : Coeff) (inside : i.val<10) :
    PV_RDCD3_CB_OwnedMaskFill.step data PV_RDCD3_CB_OwnedMaskFill.maskExponents i coeff =
      PV_RDCD3_CB_MaskCell.cell data PV_RDCD3_CB_MaskIndices.S.maskFactors i coeff := by
  rw [PV_RDCD3_CB_MaskExponentTables.mask]
  exact PV_RDCD3_CB_FillCellEq.cell data _ i coeff inside
#print axioms c1
#print axioms mask
end R1Z.PV_RDCD3_CB_FillStepsEq
