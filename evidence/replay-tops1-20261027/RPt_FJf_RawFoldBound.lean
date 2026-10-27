import RPt_FJf_RawArithmetic
set_option autoImplicit false
namespace AspisR1.FJf_RawFoldBound
open Aeneas Aeneas.Std

theorem small (n : Nat) (hn : n≤9223372028264841218) :
    JFv_TX2_FoldValue.value n≤6442450941 := by
  have hm := Nat.mod_lt n (by decide : 0 < 2147483648)
  unfold JFv_TX2_FoldValue.value
  omega

theorem typed (x : U64) (hx : x.val≤9223372028264841218) :
    (FIo_ReduceBounds.fold x).val≤6442450941 := by
  rw [JFv_TX2_FoldValue.source]
  exact small _ hx
#print axioms small
#print axioms typed
end AspisR1.FJf_RawFoldBound
