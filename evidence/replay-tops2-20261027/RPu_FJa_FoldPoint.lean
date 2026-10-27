import RPu_FJa_FoldShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_FoldPoint
open FIv_NativeValue (K)
/-- The literal address of both children determines the new low bit. -/
theorem value (c : K) (f : Nat → K) (n j : Nat) (hj : j<2*n) :
    FJa_SplitModel.fold c n f j =
      (if j%2=0 then 1-c else c)*f (j/2) := by
  have hi : j/2<n := by omega
  have v := FJa_FoldShape.children c f n (j/2) hi
  rcases Nat.mod_two_eq_zero_or_one j with he | he
  · have address : j=2*(j/2) := by omega
    conv_lhs => rw [address]
    rw [v.1,if_pos he]
    ring
  · have address : j=2*(j/2)+1 := by omega
    conv_lhs => rw [address]
    rw [v.2,if_neg (by omega)]
#print axioms value
end AspisR1.FJa_FoldPoint
end
