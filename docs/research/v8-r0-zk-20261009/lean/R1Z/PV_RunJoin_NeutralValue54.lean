import R1Z.PV_RunJoin_CircleNeutralResidue53
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_NeutralValue54
open PV_RunJoin_CircleNeutralShape53
abbrev M := ZMod AspisV8R19.PartialProduct.p
def scalar (x : U32) : M := x.val

theorem prime_zero : ((2147483647 : Nat) : M)=0 := ZMod.natCast_self _
theorem injective (a b : U32) (ha : Canon a) (hb : Canon b) (h : scalar a=scalar b) : a=b := by
  have hv := congrArg ZMod.val h
  change a.val%2147483647=b.val%2147483647 at hv
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hv
  exact UScalar.eq_of_val_eq hv

theorem residue (y : U32) (n : Nat) (h : y.val=n%2147483647) : scalar y=(n : M) := by
  unfold scalar
  rw [h]
  exact ZMod.natCast_mod n AspisV8R19.PartialProduct.p

theorem subtract (x : U32) (hx : x.val<4294967294) :
    scalar (PV_RunJoin_CircleNeutralSubtract53.output x)=scalar x := by
  unfold scalar
  rw [PV_RunJoin_CircleNeutralSubtract53.value]
  split
  · rw [Nat.cast_sub (by assumption),prime_zero,sub_zero]
  · rfl

theorem fold (n : Nat) : (AspisV8R19.PartialProduct.foldOnce n : M)=(n : M) :=
  AspisV8R19.PartialProduct.partial_cast n
#print axioms scalar
#print axioms prime_zero
#print axioms injective
#print axioms residue
#print axioms subtract
#print axioms fold
end R1Z.PV_RunJoin_NeutralValue54
