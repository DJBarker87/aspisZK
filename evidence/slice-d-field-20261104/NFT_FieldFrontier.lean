import NFT_ChannelFour
set_option autoImplicit false
namespace NFT_FieldFrontier
/-- Four canonical products stay within U64. This supplies the missing fourth
iteration budget; it does not claim the still-open helper source association. -/
theorem products_bound (products : List Nat)
    (bounded : ∀ p ∈ products, p≤(2147483647-1)^2) :
    products.sum≤products.length*(2147483647-1)^2 := by
  induction products with
  | nil => simp
  | cons p ps ih =>
    have hp:=bounded p (by simp)
    have hs:=ih (by intro q h;exact bounded q (by simp [h]))
    calc
      (p::ps).sum≤(2147483647-1)^2+ps.length*(2147483647-1)^2 := Nat.add_le_add hp hs
      _=(p::ps).length*(2147483647-1)^2 := by simp [Nat.succ_mul,Nat.add_comm]

theorem four_fit (products : List Nat) (length : products.length≤4)
    (bounded : ∀ p ∈ products, p≤(2147483647-1)^2) : products.sum<2^64 := by
  have h:=products_bound products bounded
  have hmul:=Nat.mul_le_mul_right ((2147483647-1)^2) length
  exact lt_of_le_of_lt (Nat.le_trans h hmul) (by norm_num)
#print axioms products_bound
#print axioms four_fit
end NFT_FieldFrontier
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for n in [`AspisR1SelectedMaskProbe.field.qm31_accumulate_product_channels,
           `AspisR1SelectedMaskProbe.field.qm31_sum_products_small,
           `FIq_Native.field.qm31_accumulate_product_channels,
           `FIq_Native.field.qm31_sum_products_small] do
  logInfo m!"FRONTIER_DEFINITION {n} present={env.contains n}"
