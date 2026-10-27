import R1Z.PV_AL_PopLast
import R1Z.PV_AL_RemoveModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_AL_MoveFacts
set_option autoImplicit false

theorem sub_value (x y : Usize) (h : y.val ≤ x.val) :
    (Usize.wrapping_sub x y).val=x.val-y.val := by
  change (x.bv-y.bv).toNat=_
  exact BitVec.toNat_sub_of_le h

theorem last_value {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    (Usize.wrapping_sub (alloc.vec.Vec.len v) 1#usize).val=v.val.length-1 := by
  have hn : 0 < v.val.length := by cases hv : v.val <;> simp_all
  exact sub_value (alloc.vec.Vec.len v) 1#usize (by change 1 ≤ v.val.length; omega)

theorem last_bound {T : Type} (v : alloc.vec.Vec T) (h : v.val ≠ []) :
    v.val.length-1 < v.val.length := by cases hv : v.val <;> simp_all

theorem zero_copy (n : Nat) (h : 0<n) : n-(n-1)-1=0 := by omega

theorem one_past (n cap : Nat) (h : 0<n) (hc : n ≤ cap) : (n-1)+1 ≤ cap := by omega

theorem empty_suffix {T : Type} (xs : List T) (h : xs ≠ []) :
    xs.drop (xs.length-1+1)=[] := by
  have hn : 0<xs.length := by cases xs <;> simp_all
  rw [show xs.length-1+1=xs.length by omega,List.drop_length]

#print axioms sub_value
#print axioms last_value
#print axioms last_bound
#print axioms zero_copy
#print axioms one_past
#print axioms empty_suffix
end R1Z.PV_AL_MoveFacts
