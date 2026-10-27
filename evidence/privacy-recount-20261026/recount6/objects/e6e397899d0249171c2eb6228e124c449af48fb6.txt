import R1Z.PV_AL_RangeSource
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_SplitWords
set_option autoImplicit false

theorem quotient (v : Slice U8) (size : Usize) (hs : size.val ≠ 0) :
    ∃ q, Slice.len v / size=ok q ∧ q.val=v.val.length/size.val := by
  exact UScalar.div_spec (Slice.len v) hs

theorem consumed (v : Slice U8) (size q : Usize)
    (hq : q.val=v.val.length/size.val) :
    (Usize.wrapping_mul q size).val=(v.val.length/size.val)*size.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (q.val*size.val)%UScalar.size .Usize=(v.val.length/size.val)*size.val
  rw [hq]
  apply Nat.mod_eq_of_lt
  have h := (Slice.len v).hSize
  change v.val.length < UScalar.size .Usize at h
  exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) h

theorem bound (v : Slice U8) (size q : Usize)
    (hq : q.val=v.val.length/size.val) :
    (Usize.wrapping_mul q size).val ≤ v.val.length := by
  rw [consumed v size q hq]
  exact Nat.div_mul_le_self _ _

#print axioms quotient
#print axioms consumed
#print axioms bound
end R1Z.PV_AL_SplitWords
