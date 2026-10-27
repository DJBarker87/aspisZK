import FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_Constants
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge

theorem zero : FIo_WideValues.Canon FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO ∧
    decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=0 := by
  constructor
  · simp [FIo_WideValues.Canon,FIo_QMValues.Canon,FIo_CMValues.Canon,
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

theorem one : FIo_WideValues.Canon FIo_Native.aspis_core.field.wide_exact.WideExact.ONE ∧
    decodeWide (wide FIo_Native.aspis_core.field.wide_exact.WideExact.ONE)=1 := by
  constructor
  · simp [FIo_WideValues.Canon,FIo_QMValues.Canon,FIo_CMValues.Canon,
      FIo_Native.aspis_core.field.wide_exact.WideExact.ONE,FIo_Native.aspis_core.field.QM31.ONE,
      FIo_Native.aspis_core.field.QM31.ZERO]
  · apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

#print axioms zero
#print axioms one
end AspisR1.FIo_Constants
end
