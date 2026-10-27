import RPt_FJf_Raw01
import RPt_JFv_TX2_FoldResidue
set_option autoImplicit false
namespace AspisR1.FJf_RawResidue
open Aeneas Aeneas.Std
open FJf_RawReference FJf_RawArithmetic
abbrev F := ZMod 2147483647

theorem fold (n : Nat) : (JFv_TX2_FoldValue.value n : F)=(n : F) := by
  calc
    _ = ((JFv_TX2_FoldValue.value n%2147483647 : Nat) : F) := (ZMod.natCast_mod _ _).symm
    _ = ((n%2147483647 : Nat) : F) := congrArg (fun x : Nat => (x : F)) (JFv_TX2_FoldResidue.source n)
    _ = _ := ZMod.natCast_mod _ _

theorem pp : ((4611686014132420609 : Nat) : F)=0 := by
  change ((2147483647*2147483647 : Nat) : F)=0
  rw [Nat.cast_mul,ZMod.natCast_self,zero_mul]

theorem triple_p : ((6442450941 : Nat) : F)=0 := by
  change ((3*2147483647 : Nat) : F)=0
  rw [Nat.cast_mul,ZMod.natCast_self,mul_zero]

theorem twice_pp : ((9223372028264841218 : Nat) : F)=0 := by
  change ((2147483647*(2*2147483647) : Nat) : F)=0
  rw [Nat.cast_mul,ZMod.natCast_self,zero_mul]

theorem u_value (c d g h : U32)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((u c d g h).val : F)=(c.val : F)*(g.val : F)-(d.val : F)*(h.val : F) := by
  have bd := product_bound d h hd hh
  have safety : d.val*h.val≤c.val*g.val+4611686014132420609 := by omega
  rw [(FJf_RawUV.u_value c d g h hc hd hg hh).1,fold,Nat.cast_sub safety,
    Nat.cast_add,Nat.cast_mul,Nat.cast_mul,pp,add_zero]

theorem v_value (c d g h : U32)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647)
    (hg : g.val < 2147483647) (hh : h.val < 2147483647) :
    ((v c d g h).val : F)=(c.val : F)*(h.val : F)+(d.val : F)*(g.val : F) := by
  rw [(FJf_RawUV.v_value c d g h hc hd hg hh).1,fold,Nat.cast_add,Nat.cast_mul,Nat.cast_mul]
#print axioms fold
#print axioms pp
#print axioms triple_p
#print axioms twice_pp
#print axioms u_value
#print axioms v_value
end AspisR1.FJf_RawResidue
