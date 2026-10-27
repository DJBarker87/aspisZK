import RPv_FJm_SquareAlgebra
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
namespace AspisR1.FJm_ModSquare

theorem value (p a b : Nat) [Fact p.Prime] (hb : b≤a+p) :
    (((a+b)*(a+p-b) : Nat) : ZMod p)=
      (a : ZMod p)*(a : ZMod p)+(-1)*(b : ZMod p)*(b : ZMod p) := by
  rw [Nat.cast_mul,Nat.cast_add,Nat.cast_sub hb,Nat.cast_add,ZMod.natCast_self,add_zero]
  exact FJm_SquareAlgebra.real _ _
#print axioms value
end AspisR1.FJm_ModSquare
