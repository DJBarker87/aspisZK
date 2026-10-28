import NDD_ScalarCanon
import NDD_Prepared
import ExtractedMaskM31AddSub
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_ReferenceLinear
abbrev P : Nat := 2147483647

theorem add (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    NDD_Reference.add_ref x y = FIn_WeightsExtract.field.M31.add x y := by
  change x.val < 2147483647 at hx
  change y.val < 2147483647 at hy
  unfold NDD_Reference.add_ref FIn_WeightsExtract.field.M31.add FIn_WeightsExtract.field.P
  rw [NDD_ScalarCanon.checked_add x y (by omega)]
  simp only [lift,bind_tc_ok]
  split
  · exact NDD_ScalarCanon.checked_sub _ _ (by scalar_tac)
  · rfl

theorem sub (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    NDD_Reference.sub_ref x y = FIn_WeightsExtract.field.M31.sub x y := by
  change x.val < 2147483647 at hx
  change y.val < 2147483647 at hy
  unfold NDD_Reference.sub_ref FIn_WeightsExtract.field.M31.sub FIn_WeightsExtract.field.P
  rw [NDD_ScalarCanon.checked_add x 2147483647#u32 (by scalar_tac)]
  simp only [lift,bind_tc_ok]
  have h : y.val ≤ (U32.wrapping_add x 2147483647#u32).val := by
    have hb : x.val + (2147483647#u32).val < UScalar.size .U32 := by scalar_tac
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt hb]
    scalar_tac
  rw [NDD_ScalarCanon.checked_sub _ y h]
  simp only [lift,bind_tc_ok]
  split
  · exact NDD_ScalarCanon.checked_sub _ _ (by scalar_tac)
  · rfl

theorem add_canonical (x y : U32) (hx : x.val < P) (hy : y.val < P) :
    ∃ z, FIn_WeightsExtract.field.M31.add x y = ok z ∧ z.val < P := by
  obtain ⟨z,hz,_,hc⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x y hx hy
  exact ⟨z, (add x y hx hy).symm.trans ((NDD_Prepared.add_reference x y).trans hz), hc⟩

#print axioms add
#print axioms sub
#print axioms add_canonical
end NDD_ReferenceLinear
