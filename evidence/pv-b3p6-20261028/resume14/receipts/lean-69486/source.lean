import PV_B3P_MaskWhile14227
namespace PV_B3P_Correct14227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
/-- A 16-bit integer-control cell only; no field term is reduced. -/
theorem clear_2048_14 : clear_times14 16 2048 = 0 := by decide

theorem mask_while_2048_14 (values : Array aspis_core.field.QM31 16#usize) :
    mask_while14 values 2048 aspis_core.field.QM31.ZERO =
      PV_B3P_Binding11227.source_mask11 values 2048#u16 :=
  mask_while_walk14 values 16 2048 aspis_core.field.QM31.ZERO clear_2048_14
#print axioms clear_2048_14
#print axioms mask_while_2048_14
end PV_B3P_Correct14227
