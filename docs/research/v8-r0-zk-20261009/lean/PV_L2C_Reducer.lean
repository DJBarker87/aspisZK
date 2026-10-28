import PV_L2C_M31
set_option autoImplicit false
namespace PV_L2C_Reducer
open PV_L2C_M31
/-- Integer image of `(x & P) + (x >> 31)`. -/
def fold31 (x : Nat) : Nat := x % (p+1)+x/(p+1)

theorem first_bound (x : Nat) (hx : x<2^64) : fold31 x<5*(p+1) := by
  have hm := Nat.mod_lt x (show 0<p+1 by omega)
  unfold fold31 p at *
  omega
#print axioms first_bound

theorem second_bound (x : Nat) (hx : x<2^64) : fold31 (fold31 x)<p+5 := by
  have h := first_bound x hx
  have hm := Nat.mod_lt (fold31 x) (show 0<p+1 by omega)
  unfold fold31 p at *
  omega
#print axioms second_bound

theorem fold_decode (x : Nat) : (fold31 x : ZMod p)=(x : ZMod p) := by
  have h := congrArg (fun n : Nat => (n : ZMod p)) (Nat.mod_add_div x (p+1))
  have hr : ((p+1 : Nat) : ZMod p)=1 := by rw [Nat.cast_add,ZMod.natCast_self]; simp
  rw [Nat.cast_add,Nat.cast_mul,hr,one_mul] at h
  simpa only [fold31,Nat.cast_add] using h
#print axioms fold_decode

theorem reduction_bound (x : Nat) (hx : x<2^64) : fold31 (fold31 x)<2*p := by
  have h := second_bound x hx
  unfold p at *
  omega
#print axioms reduction_bound
end PV_L2C_Reducer
