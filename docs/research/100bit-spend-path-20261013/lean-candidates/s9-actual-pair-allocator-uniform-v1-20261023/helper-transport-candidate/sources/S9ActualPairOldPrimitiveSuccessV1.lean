import S9ActualPairOldCarrierScalarV1
import S9ActualPairSquareHelperTransportV1
import S9ActualPairMixedHelperTransportV1
import S9ActualPairWideAddHelperTransportV1
import S9ActualPairMulM31HelperTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairOldPrimitiveSuccessV1
open AspisR1S9ActualPairOldCarrierScalarV1
abbrev QC := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical

theorem one_maps : toOldQ aspis_core.field.QM31.ONE = AspisR1S9PairCallerStepV1.field.QM31.ONE := by
  unfold aspis_core.field.QM31.ONE AspisR1S9PairCallerStepV1.field.QM31.ONE
  rfl

theorem zero_maps : toOldW aspis_core.field.wide_exact.WideExact.ZERO = AspisR1S9PairCallerStepV1.field.WideExact.ZERO := by
  unfold aspis_core.field.wide_exact.WideExact.ZERO AspisR1S9PairCallerStepV1.field.WideExact.ZERO
    aspis_core.field.QM31.ZERO AspisR1S9PairCallerStepV1.field.QM31.ZERO
  rfl

theorem qm_mul_success (x y z : Q) (hx : QC x) (hy : QC y)
    (h : aspis_core.field.QM31.mul x y = .ok z) :
    AspisR1S9PairCallerStepV1.field.QM31.mul (toOldQ x) (toOldQ y) = .ok (toOldQ z) := by
  have hm := AspisR1S9ActualPairQMHelperTransportV1.actual_pair_qm_mul_to_installed_helper x y hx hy
  rw [h] at hm
  change .ok (toHelperQ z) = @AspisR1S9HelperP6.FieldOps.qmMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperQ x) (toHelperQ y) at hm
  unfold AspisR1S9PairCallerStepV1.field.QM31.mul
  simp only [toP6Q_toOldQ]
  rw [←hm]
  rfl

theorem qm_square_success (x z : Q) (hx : QC x)
    (h : aspis_core.field.QM31.square x = .ok z) :
    AspisR1S9PairCallerStepV1.field.QM31.square (toOldQ x) = .ok (toOldQ z) := by
  have hm := AspisR1S9ActualPairSquareHelperTransportV1.actual_pair_qm_square_to_installed_helper x hx
  rw [h] at hm
  change .ok (toHelperQ z) = @AspisR1S9HelperP6.FieldOps.qmSquare
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperQ x) at hm
  unfold AspisR1S9PairCallerStepV1.field.QM31.square
  simp only [toP6Q_toOldQ]
  rw [←hm]
  rfl

theorem wide_add_success (x y z : W) (hx : WC x) (hy : WC y)
    (h : aspis_core.field.wide_exact.WideExact.add x y = .ok z) :
    AspisR1S9PairCallerStepV1.field.WideExact.add (toOldW x) (toOldW y) = .ok (toOldW z) := by
  have hm := AspisR1S9ActualPairWideAddHelperTransportV1.actual_pair_wide_add_to_installed_helper x y hx hy
  rw [h] at hm
  change .ok (toHelperW z) = @AspisR1S9HelperP6.FieldOps.wideAdd
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperW x) (toHelperW y) at hm
  unfold AspisR1S9PairCallerStepV1.field.WideExact.add
  simp only [toP6W_toOldW]
  rw [←hm]
  rfl

theorem wide_mul_success (x y z : W) (hx : WC x) (hy : WC y)
    (h : aspis_core.field.wide_exact.WideExact.mul x y = .ok z) :
    AspisR1S9PairCallerStepV1.field.WideExact.mul (toOldW x) (toOldW y) = .ok (toOldW z) := by
  have hm := AspisR1S9ActualPairWideHelperTransportV1.actual_pair_wide_mul_to_installed_helper x y hx hy
  rw [h] at hm
  change .ok (toHelperW z) = @AspisR1S9HelperP6.FieldOps.wideMul
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperW x) (toHelperW y) at hm
  unfold AspisR1S9PairCallerStepV1.field.WideExact.mul
  simp only [toP6W_toOldW]
  rw [←hm]
  rfl

theorem wide_mul_m31_success (x z : W) (scalar : U32)
    (h : aspis_core.field.wide_exact.WideExact.mul_m31 x scalar = .ok z) :
    AspisR1S9PairCallerStepV1.field.WideExact.mul_m31 (toOldW x) scalar = .ok (toOldW z) := by
  have hm := AspisR1S9ActualPairMulM31HelperTransportV1.actual_pair_wide_mul_m31_to_installed_helper x scalar
  rw [h] at hm
  change .ok (toHelperW z) = @AspisR1S9HelperP6.FieldOps.wideMulM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperW x) scalar at hm
  unfold AspisR1S9PairCallerStepV1.field.WideExact.mul_m31
  simp only [toP6W_toOldW, AspisR1S9PairCallerStepV1.toP6M]
  rw [←hm]
  rfl

theorem wide_mul_qm31_success (x z : W) (q : Q) (hx : WC x)
    (h : aspis_core.field.wide_exact.WideExact.mul_qm31 x q = .ok z) :
    AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 (toOldW x) (toOldQ q) = .ok (toOldW z) := by
  have hm := AspisR1S9ActualPairMixedHelperTransportV1.actual_pair_wide_mul_qm31_to_installed_helper x q hx
  rw [h] at hm
  change .ok (toHelperW z) = @AspisR1S9HelperP6.FieldOps.wideMulQM31
    AspisR1S9ConcreteFieldOpsV1.concreteFieldOps (toHelperW x) (toHelperQ q) at hm
  unfold AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31
  simp only [toP6W_toOldW,toP6Q_toOldQ]
  rw [←hm]
  rfl
#print axioms qm_mul_success
#print axioms qm_square_success
#print axioms wide_add_success
#print axioms wide_mul_success
#print axioms wide_mul_m31_success
#print axioms wide_mul_qm31_success
#print axioms one_maps
#print axioms zero_maps
end AspisR1S9ActualPairOldPrimitiveSuccessV1
