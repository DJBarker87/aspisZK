import R1Z.PV_B2_Total_QM31_mul
import R1Z.PV_RDB2D_SparseWeights
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawOps
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev valueAdd := PV_B2_FieldValue.aspis_core.field.QM31.add
abbrev valueMul := PV_B2_FieldValue.aspis_core.field.QM31.mul
abbrev valueSub := PV_B2_FieldValue.aspis_core.field.QM31.sub
abbrev zero := PV_B2_FieldValue.aspis_core.field.QM31.ZERO
abbrev one := PV_B2_FieldValue.aspis_core.field.QM31.ONE
/-- The actual ordered Result methods, on all four raw u32 limbs. -/
def ops : PV_RDB2D_SparseWeights.WeightOps Q :=
 {zero:=PV_B2_WeightsNative.aspis_core.field.QM31.ZERO
  one:=PV_B2_WeightsNative.aspis_core.field.QM31.ONE
  mul:=PV_B2_WeightsNative.aspis_core.field.QM31.mul
  add:=PV_B2_WeightsNative.aspis_core.field.QM31.add
  subOne:=fun q=>PV_B2_WeightsNative.aspis_core.field.QM31.sub
   PV_B2_WeightsNative.aspis_core.field.QM31.ONE q}

theorem mul (a b : Q) : ops.mul a b=ok (valueMul a b) := PV_B2_FieldTotal.QM31_mul a b
theorem add (a b : Q) : ops.add a b=ok (valueAdd a b) := PV_B2_FieldTotal.QM31_add a b
theorem sub (a : Q) : ops.subOne a=ok (valueSub one a) := by
 change PV_B2_WeightsNative.aspis_core.field.QM31.sub _ _=_
 rw [PV_B2_FieldTotal.QM31_sub,PV_B2_FieldTotal.QM31_ONE]
theorem zero_value : ops.zero=zero := PV_B2_FieldTotal.QM31_ZERO
theorem one_value : ops.one=one := PV_B2_FieldTotal.QM31_ONE
#print axioms mul
#print axioms add
#print axioms sub
#print axioms zero_value
#print axioms one_value
end R1Z.PV_OWNI_RawOps
