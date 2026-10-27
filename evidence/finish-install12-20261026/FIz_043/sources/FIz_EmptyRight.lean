import FIz_EmptyBound
import FIy_DigestLane
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_EmptyRight
open FIv_NativeValue (K)
theorem value (level : Fin 20) (j : Fin 8) :
    (FIy_DigestLane.target (FIy_FrontierMeaning.roots level.val) true j.val : K)=
      R0P.emptyRootRightTarget level j := by
  unfold FIy_DigestLane.target FIy_DigestTarget.value
  rw [FIz_EmptyRoots.table level.castSucc j]
  unfold R0P.emptyRootRightTarget
  have bound := FIz_EmptyBound.value level.castSucc j
  have shape : j.val+1=8 ↔ j.val=7 := by omega
  rw [shape]
  by_cases hj : j.val=7
  · simp only [hj,↓reduceIte,true_and]
    change (((R0P.emptyRootsNat level.castSucc j+1095962629)%2147483647 : Nat) : K) = _
    split_ifs with hb
    · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  · simp only [hj,↓reduceIte,and_false]
#print axioms value
end AspisR1.FIz_EmptyRight
end
