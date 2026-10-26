import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.FIo_ScalarBridge

theorem add {ty : UScalarTy} (x y : UScalar ty)
    (h : x.val+y.val < UScalar.size ty) :
    x+y=ok (UScalar.wrapping_add x y) := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by simp only [UScalar.max]; simp only [UScalar.size] at h; omega))
  have he : z=UScalar.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt h]
    exact hval
  simpa only [he] using hz

theorem sub {ty : UScalarTy} (x y : UScalar ty) (h : y.val≤x.val) :
    x-y=ok (UScalar.wrapping_sub x y) := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists (UScalar.sub_spec (x:=x) (y:=y) h)
  have he : z=UScalar.wrapping_sub x y := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.wrapping_sub_val_eq]
    have hx := x.hSize
    have hy := y.hSize
    have rearrange : x.val+(UScalar.size ty-y.val)=(x.val-y.val)+UScalar.size ty := by omega
    rw [rearrange,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
    exact hval
  simpa only [he] using hz

theorem mul {ty : UScalarTy} (x y : UScalar ty)
    (h : x.val*y.val<UScalar.size ty) :
    x*y=ok (UScalar.wrapping_mul x y) := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y)
    (by simp only [UScalar.max]; simp only [UScalar.size] at h; omega))
  have he : z=UScalar.wrapping_mul x y := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.wrapping_mul_val_eq,Nat.mod_eq_of_lt h]
    exact hval
  simpa only [he] using hz

#print axioms add
#print axioms sub
#print axioms mul
end AspisR1.FIo_ScalarBridge
