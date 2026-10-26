import R1Z.PV_CB_CurrentQuartic
import R1Z.PV_CB_CurrentNeg
import R1Z.ProverRwSuccessQuarticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CurrentTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
open ProverRwDictionaryTower
namespace S
abbrev mAdd := ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev mSub := ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
abbrev mMul := ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev mDouble := ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
abbrev cAdd := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.add
abbrev cSub := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
abbrev cMul := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul
abbrev cDouble := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.double
abbrev cScale := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31
abbrev cSquare := ProverRwP7CurrentFieldSource.aspis_core.field.CM31.square
abbrev cR := ProverRwP7CurrentFieldSource.aspis_core.field.mul_by_r
abbrev qAdd := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev qMul := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev qSquare := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square
abbrev qScale := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
end S
theorem m_add (a b : U32) : Total (S.mAdd a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (ProverRwP7CurrentBaseBridge.add a b)).mpr
    (ProverRwSuccessArithmeticTotal.m_add a b)
theorem m_sub (a b : U32) : Total (S.mSub a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (ProverRwP7CurrentBaseBridge.sub a b)).mpr
    (ProverRwSuccessArithmeticTotal.m_sub a b)
theorem m_mul (a b : U32) : Total (S.mMul a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (ProverRwP7CurrentBaseBridge.mul a b)).mpr
    (ProverRwSuccessArithmeticTotal.m_mul a b)
theorem m_double (a : U32) : Total (S.mDouble a) := m_add a a
theorem c_add (a b : C) : Total (S.cAdd a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentComplex.add a b)).mpr
    (mapped_total _ _ (ProverRwSuccessQuarticTotal.c_add _ _))
theorem c_sub (a b : C) : Total (S.cSub a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentComplex.sub a b)).mpr
    (mapped_total _ _ (ProverRwSuccessArithmeticTotal.c_sub _ _))
theorem c_mul (a b : C) : Total (S.cMul a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentComplex.mul a b)).mpr
    (mapped_total _ _ (ProverRwSuccessArithmeticTotal.c_mul _ _))
theorem c_double (a : C) : Total (S.cDouble a) := c_add a a
theorem c_r (a : C) : Total (S.cR a) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentQuartic.r a)).mpr
    (mapped_total _ _ (ProverRwSuccessQuarticTotal.c_r _))
theorem c_scale (a : C) (b : U32) : Total (S.cScale a b) := by
  unfold S.cScale ProverRwP7CurrentFieldSource.aspis_core.field.CM31.mul_m31
  apply bind_total (m_mul _ _);intro _
  apply bind_total (m_mul _ _);intro _
  exact ok_total _
theorem c_square (a : C) : Total (S.cSquare a) := by
  apply (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentComplexMore.square a)).mpr
  apply mapped_total
  unfold AspisR1ProducerRelease47.field.CM31.square
  simp only [lift,bind_tc_ok]
  apply bind_total (ProverRwSuccessArithmeticTotal.m_reduce _);intro _
  apply bind_total (ProverRwSuccessArithmeticTotal.m_mul _ _);intro _
  apply bind_total (ProverRwSuccessQuarticTotal.m_double _);intro _
  exact ok_total _
theorem q_add (a b : Q) : Total (S.qAdd a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentQuartic.add a b)).mpr
    (mapped_total _ _ (ProverRwSuccessQuarticTotal.q_add _ _))
theorem q_mul (a b : Q) : Total (S.qMul a b) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total (PV_CB_CurrentQuartic.mul a b)).mpr
    (mapped_total _ _ (ProverRwSuccessQuarticTotal.q_mul _ _))
theorem q_square (a : Q) : Total (S.qSquare a) := by
  unfold S.qSquare ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square
  apply bind_total (c_square _);intro _
  apply bind_total (c_square _);intro _
  apply bind_total (c_r _);intro _
  apply bind_total (c_add _ _);intro _
  apply bind_total (c_mul _ _);intro _
  apply bind_total (c_double _);intro _
  exact ok_total _
theorem q_scale (a : Q) (b : U32) : Total (S.qScale a b) := by
  unfold S.qScale ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
  apply bind_total (c_scale _ _);intro _
  apply bind_total (c_scale _ _);intro _
  exact ok_total _
#print axioms m_add
#print axioms m_sub
#print axioms m_mul
#print axioms m_double
#print axioms c_add
#print axioms c_sub
#print axioms c_mul
#print axioms c_double
#print axioms c_r
#print axioms c_scale
#print axioms c_square
#print axioms q_add
#print axioms q_mul
#print axioms q_square
#print axioms q_scale
end R1Z.PV_CB_CurrentTotal
