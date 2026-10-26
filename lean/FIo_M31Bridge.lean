import FIo_FieldBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_M31Bridge
open Aeneas Aeneas.Std Result

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1CurrentWide.field.M31.add x y := by
  have hadd : x+y=ok (U32.wrapping_add x y) :=
    FIo_ScalarBridge.add x y (by scalar_tac)
  simp only [FIo_Native.aspis_core.field.M31.add,AspisR1CurrentWide.field.M31.add,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,hadd,lift,bind_tc_ok]
  split
  · rename_i h
    have hs : (2147483647#u32).val≤(U32.wrapping_add x y).val := by scalar_tac
    have hsub := FIo_ScalarBridge.sub (U32.wrapping_add x y) (2147483647#u32) hs
    rw [hsub]
    rfl
  · rfl

#print axioms add
end AspisR1.FIo_M31Bridge
end
