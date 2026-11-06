import NKJ_Extracted.Funs
import NGA_Cache
set_option autoImplicit false
namespace NKJ_Wrap32
open Aeneas Aeneas.Std Result

theorem add_wrap (a b : U32) (h : a.val+b.val<2^32) :
 (U32.wrapping_add a b).val=a.val+b.val := by
 rw [U32.wrapping_add_val_eq]
 apply Nat.mod_eq_of_lt
 rw [UScalar.size_def]
 scalar_tac

theorem sub_wrap (a b : U32) (h : b.val≤a.val) :
 (U32.wrapping_sub a b).val=a.val-b.val := by
 rw [U32.wrapping_sub_val_eq]
 have hb : a.val<UScalar.size .U32 := by simpa only [UScalar.size] using a.hBounds
 have he : a.val+(UScalar.size .U32-b.val)=(a.val-b.val)+UScalar.size .U32 := by omega
 rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
 exact Nat.mod_eq_of_lt (by omega)

theorem add (a b : U32) (ha : a.val<2147483647) (hb : b.val<2147483647) :
 NKJ_Extracted.field.NKJ_reference.NKJ_add a b=AspisR1SelectedMaskProbe.field.M31.add a b := by
 obtain ⟨q,hq,hv,_⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod a b ha hb
 let s := U32.wrapping_add a b
 have hs : s.val=a.val+b.val := add_wrap a b (by omega)
 let z := if 2147483647≤s.val then U32.wrapping_sub s 2147483647#u32 else s
 have hz : z.val=(a.val+b.val)%2147483647 := by
  by_cases h : 2147483647≤s.val
  · simp only [z,if_pos h]
    rw [sub_wrap s 2147483647#u32 (by change 2147483647≤s.val;exact h)]
    change s.val-2147483647=(a.val+b.val)%2147483647
    rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [z,if_neg h]
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hs
 have same : z=q := UScalar.eq_of_val_eq (hz.trans hv.symm)
 rw [hq,←same]
 change (if s >= NKJ_Extracted.field.P then ok (U32.wrapping_sub s NKJ_Extracted.field.P) else ok s)=ok z
 rw [NKJ_Extracted.field.P]
 change (if 2147483647≤s.val then ok (U32.wrapping_sub s 2147483647#u32) else ok s)=ok z
 by_cases h : 2147483647≤s.val <;> simp only [z,h,if_true,if_false]
#print axioms add_wrap
#print axioms sub_wrap
#print axioms add
end NKJ_Wrap32
