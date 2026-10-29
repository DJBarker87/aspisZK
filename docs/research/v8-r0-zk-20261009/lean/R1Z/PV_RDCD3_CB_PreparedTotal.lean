import R1Z.PV_RDCD3_FieldTotal
import R1Z.PV_RDCD3_ArrayRead
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_PreparedTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total
namespace S
abbrev newPart := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
abbrev new := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.new
abbrev mulPart := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
abbrev mul := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul
end S
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Prepared := PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier
theorem new_part (x : C) : Total (S.newPart () x) := by
  unfold S.newPart PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
  apply bind_total (PV_RDCD3_FieldTotal.m_add _ _);intro _
  exact ok_total _
theorem new (x : Q) : Total (S.new x) := by
  unfold S.new PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.new
  apply bind_total (new_part _);intro _
  apply bind_total (new_part _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.c_add _ _);intro _
  apply bind_total (new_part _);intro _
  exact ok_total _
theorem mul_part (left : Array U32 3#usize) (right : C) :
    Total (S.mulPart () (left,right)) := by
  unfold S.mulPart PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  apply bind_total (PV_RDCD3_ArrayRead.read left 0#usize (by decide));intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_mul _ _);intro _
  apply bind_total (PV_RDCD3_ArrayRead.read left 1#usize (by decide));intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_mul _ _);intro _
  apply bind_total (PV_RDCD3_ArrayRead.read left 2#usize (by decide));intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_add _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_mul _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_sub _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_sub _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.m_sub _ _);intro _
  exact ok_total _
theorem mul (p : Prepared) (x : Q) : Total (S.mul p x) := by
  unfold S.mul PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul
  apply bind_total (PV_RDCD3_ArrayRead.read p.components 0#usize (by decide));intro a
  apply bind_total (mul_part a _);intro _
  apply bind_total (PV_RDCD3_ArrayRead.read p.components 1#usize (by decide));intro b
  apply bind_total (mul_part b _);intro _
  apply bind_total (PV_RDCD3_ArrayRead.read p.components 2#usize (by decide));intro c
  apply bind_total (PV_RDCD3_FieldTotal.c_add _ _);intro d
  apply bind_total (mul_part c d);intro _
  apply bind_total (PV_RDCD3_FieldTotal.c_r _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.c_add _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.c_sub _ _);intro _
  apply bind_total (PV_RDCD3_FieldTotal.c_sub _ _);intro _
  exact ok_total _
#print axioms new_part
#print axioms new
#print axioms mul_part
#print axioms mul
end R1Z.PV_RDCD3_CB_PreparedTotal
