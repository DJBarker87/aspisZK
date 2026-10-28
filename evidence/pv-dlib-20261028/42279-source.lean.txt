import R1Z.PV_CBL_PaddingBranch
import R1Z.PV_CBL_ShaPadFixed
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_PadBranchValue
set_option autoImplicit false
theorem remaining (pos : Usize) (hp : pos.val<64) :
    (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize).val = 64-pos.val-1 := by
  rw [Usize.wrapping_sub_val_eq]
  have h1 : (Usize.wrapping_sub 64#usize pos).val = 64-pos.val := by
    rw [Usize.wrapping_sub_val_eq]
    change (64+(UScalar.size .Usize-pos.val))%UScalar.size .Usize=64-pos.val
    have hmax := (64#usize).hSize
    change 64 < UScalar.size .Usize at hmax
    have he : 64+(UScalar.size .Usize-pos.val)=UScalar.size .Usize+(64-pos.val) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
  rw [h1]
  change (64-pos.val+(UScalar.size .Usize-1))%UScalar.size .Usize=64-pos.val-1
  have hmax := (64#usize).hSize
  change 64 < UScalar.size .Usize at hmax
  have he : 64-pos.val+(UScalar.size .Usize-1)=UScalar.size .Usize+(64-pos.val-1) := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
theorem branch (pos : Usize) (hp : pos.val<64) :
    (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize < 8#usize) ↔
      56≤pos.val := by
  change (Usize.wrapping_sub (Usize.wrapping_sub 64#usize pos) 1#usize).val < 8 ↔ _
  rw [remaining pos hp]
  omega
#print axioms remaining
#print axioms branch
end R1Z.PV_CBL_PadBranchValue
