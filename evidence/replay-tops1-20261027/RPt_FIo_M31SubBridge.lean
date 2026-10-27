import RPt_FIo_M31Bridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_M31SubBridge
open Aeneas Aeneas.Std Result

theorem sub (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.sub x y=AspisR1CurrentWide.field.M31.sub x y := by
  have hadd : x+(2147483647#u32)=ok (U32.wrapping_add x (2147483647#u32)) :=
    FIo_ScalarBridge.add x (2147483647#u32) (by scalar_tac)
  have val : (U32.wrapping_add x (2147483647#u32)).val=x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  have hsub : (U32.wrapping_add x (2147483647#u32))-y=
      ok (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) :=
    FIo_ScalarBridge.sub _ y (by rw [val]; omega)
  simp only [FIo_Native.aspis_core.field.M31.sub,AspisR1CurrentWide.field.M31.sub,
    FIo_Native.aspis_core.field.P,AspisR1CurrentWide.field.P,hadd,hsub,lift,bind_tc_ok]
  split
  · rename_i h
    have last := FIo_ScalarBridge.sub
      (U32.wrapping_sub (U32.wrapping_add x (2147483647#u32)) y) (2147483647#u32) (by scalar_tac)
    rw [last]
    rfl
  · rfl

#print axioms sub
end AspisR1.FIo_M31SubBridge
end
