import XRn_Join_Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSd_InverseShape
/-- A small arithmetic spine; there is no field normalization in its recursion. -/
def spine : Nat → Nat
 | 0 => 0
 | n+1 => 2*spine n+2

theorem even (x : U32) (n : Nat) : XRn_Join_mpow x (2*n+2) = (do
 let y ← XRn_Join_mpow x n
 aspis_core.field.M31.mul y y) := by
 have h : 2*n+2=(2*n+1)+1 := by omega
 rw [h,XRn_Join_mpow]
 have hd : (2*n+1)/2=n := by omega
 have hm : (2*n+1)%2=1 := by omega
 simp only [hd,hm,show ¬(1:Nat)=0 by decide,ite_false]
 cases XRn_Join_mpow x n with
 | fail e => rfl
 | div => rfl
 | ok y => simp only [bind_tc_ok]; cases aspis_core.field.M31.mul y y <;> rfl

theorem one_mul : aspis_core.field.M31.mul 1#u32 1#u32=ok 1#u32 := by
 rfl

theorem spine_one (x : U32) (n : Nat) : XRn_Join_mpow x (spine n)=ok 1#u32 := by
 induction n with
 | zero => simp only [spine,XRn_Join_mpow]
 | succ n ih => rw [spine,even,ih,bind_tc_ok,one_mul]

theorem inverse_spine (x : U32) (nz : x≠0#u32) :
 aspis_core.field.M31.inv x =
 aspis_core.field.M31.mul 1#u32 x := by
 unfold aspis_core.field.M31.inv
 rw [if_neg nz]
 have size : 2147483645=spine 29*2+1 := by decide
 rw [size,XRn_Join_mpow]
 have hd : (spine 29*2)/2=spine 29 := by omega
 have hm : (spine 29*2)%2=0 := by omega
 rw [hd,spine_one]
 simp only [hm,if_pos,bind_tc_ok,one_mul]
#print axioms even
#print axioms one_mul
#print axioms spine_one
#print axioms inverse_spine
end XSd_InverseShape
