import LPi_Total
import FIo_WideMulValues
import FIo_ByRValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.LPi_FieldValues
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NC NQ NE cm qm wide)

theorem cm_mul (x y : NC) (hx : FIo_CMValues.Canon x) (hy : FIo_CMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧
    FIo_CMValues.Canon z ∧ decodeC (cm z) = decodeC (cm x)*decodeC (cm y) := by
  obtain ⟨z,h⟩ := LPi_Total.cm_mul x y
  exact ⟨z,h,FIo_CMMulValues.mul x y z hx hy h⟩

theorem by_r (x : NC) (hx : FIo_CMValues.Canon x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x = ok z ∧
    FIo_CMValues.Canon z ∧ decodeC (cm z) = AspisV8R15.ExactTowerBase.qm31R*decodeC (cm x) := by
  obtain ⟨z,h⟩ := LPi_Total.by_r x
  exact ⟨z,h,FIo_ByRValues.value x z hx h⟩

theorem qm_mul (x y : NQ) (hx : FIo_QMValues.Canon x) (hy : FIo_QMValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.QM31.mul x y = ok z ∧
    FIo_QMValues.Canon z ∧ decodeQM (qm z) = decodeQM (qm x)*decodeQM (qm y) := by
  obtain ⟨z,h⟩ := LPi_Total.qm_mul x y
  exact ⟨z,h,FIo_QMMulValues.mul x y z hx hy h⟩

theorem wide_mul (x y : NE) (hx : FIo_WideValues.Canon x) (hy : FIo_WideValues.Canon y) :
    ∃ z, FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y = ok z ∧
    FIo_WideValues.Canon z ∧ decodeWide (wide z) = decodeWide (wide x)*decodeWide (wide y) := by
  obtain ⟨z,h⟩ := LPi_Total.wide_mul x y
  exact ⟨z,h,FIo_WideMulValues.mul x y z hx hy h⟩

#print axioms cm_mul
#print axioms by_r
#print axioms qm_mul
#print axioms wide_mul
end AspisR1.LPi_FieldValues
end
