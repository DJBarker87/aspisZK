import NCJ_CallLog
set_option autoImplicit false
namespace NCJ_Constants
open Aeneas Aeneas.Std AspisR1 LPi_FieldValues

theorem zero : canonE FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO := by
  simp [canonE,canonQ,canonC,LPi_CMProduct.Canon,
    FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.QM31.ZERO]

theorem one : canonQ FIo_Native.aspis_core.field.QM31.ONE := by
  simp [canonQ,canonC,LPi_CMProduct.Canon,FIo_Native.aspis_core.field.QM31.ONE]

#print axioms zero
#print axioms one
end NCJ_Constants
