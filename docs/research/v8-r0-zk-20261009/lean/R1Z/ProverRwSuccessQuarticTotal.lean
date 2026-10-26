import R1Z.ProverRwSuccessArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessQuarticTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverRwSuccessArithmeticTotal

theorem c_add (x y : field.CM31) : Total (field.CM31.add x y) := by
  unfold field.CM31.add
  apply bind_total (m_add _ _);intro _
  apply bind_total (m_add _ _);intro _
  exact ok_total _
theorem m_double (x : U32) : Total (field.M31.double x) := m_add _ _
theorem c_r (x : field.CM31) : Total (field.mul_by_r x) := by
  unfold field.mul_by_r
  apply bind_total (m_double _);intro _
  apply bind_total (m_sub _ _);intro _
  apply bind_total (m_double _);intro _
  apply bind_total (m_add _ _);intro _
  exact ok_total _
theorem q_add (x y : field.QM31) : Total (field.QM31.add x y) := by
  unfold field.QM31.add
  apply bind_total (c_add _ _);intro _
  apply bind_total (c_add _ _);intro _
  exact ok_total _
theorem q_sub (x y : field.QM31) : Total (field.QM31.sub x y) := by
  unfold field.QM31.sub
  apply bind_total (c_sub _ _);intro _
  apply bind_total (c_sub _ _);intro _
  exact ok_total _
theorem q_mul (x y : field.QM31) : Total (field.QM31.mul x y) := by
  unfold field.QM31.mul
  apply bind_total (c_mul _ _);intro _
  apply bind_total (c_mul _ _);intro _
  apply bind_total (c_add _ _);intro _
  apply bind_total (c_add _ _);intro _
  apply bind_total (c_mul _ _);intro _
  apply bind_total (c_r _);intro _
  apply bind_total (c_add _ _);intro _
  apply bind_total (c_sub _ _);intro _
  apply bind_total (c_sub _ _);intro _
  exact ok_total _
theorem add (x y : ProverRwDictionaryTower.Q) : Total (ProverRwDictionaryTower.qAdd x y) :=
  mapped_total _ _ (q_add _ _)
theorem sub (x y : ProverRwDictionaryTower.Q) : Total (ProverRwDictionaryTower.qSub x y) :=
  mapped_total _ _ (q_sub _ _)
theorem mul (x y : ProverRwDictionaryTower.Q) : Total (ProverRwDictionaryTower.qMul x y) :=
  mapped_total _ _ (q_mul _ _)
#print axioms c_add
#print axioms m_double
#print axioms c_r
#print axioms q_add
#print axioms q_sub
#print axioms q_mul
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.ProverRwSuccessQuarticTotal
