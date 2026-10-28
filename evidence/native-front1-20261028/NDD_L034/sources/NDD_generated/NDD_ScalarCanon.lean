import NDD_Reference.Funs
import NDD_ResultLaws
import FIn_WeightsFuns
import ExtractedMaskReducerOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_ScalarCanon

theorem checked_add (x y : U32) (bound : x.val+y.val < 2^32) :
    x+y = ok (U32.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := AspisR1.ExtractedMaskReducerOps.tryMk_success (ty:=.U32)
    (x.val+y.val) bound
  have hval : z.val = (U32.wrapping_add x y).val := by
    rw [hv,U32.wrapping_add_val_eq,Nat.mod_eq_of_lt bound]
  have he := congrArg (fun bv : BitVec 32 => (⟨bv⟩ : U32))
    (BitVec.eq_of_toNat_eq hval)
  simpa only [he] using hz

theorem checked_sub (x y : U32) (bound : y.val ≤ x.val) :
    x-y = ok (U32.wrapping_sub x y) := by
  obtain ⟨z,hz,hv⟩ := AspisR1.ExtractedMaskReducerOps.sub_success x y bound
  have hval : z.val = (U32.wrapping_sub x y).val := by
    rw [hv,U32.wrapping_sub_val_eq]
    scalar_tac
  have he := congrArg (fun bv : BitVec 32 => (⟨bv⟩ : U32))
    (BitVec.eq_of_toNat_eq hval)
  simpa only [he] using hz

#print axioms checked_add
#print axioms checked_sub
end NDD_ScalarCanon
