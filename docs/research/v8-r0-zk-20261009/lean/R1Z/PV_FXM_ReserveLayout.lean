import Aeneas
set_option autoImplicit false
namespace R1Z.PV_FXM_ReserveLayout
open Aeneas Aeneas.Std

/-- A native element layout is padded to alignment. For a power-of-two
alignment dividing isize::MAX+1, the source's rounded layout guard is exactly
the byte-limit guard in ReserveWorld. No rounding is silently omitted. -/
theorem aligned_limit (bytes limit align k m : Nat) (positive : 0<align)
    (padded : bytes=k*align) (target : limit+1=m*align) :
    bytes≤limit ↔ bytes≤limit+1-align := by
  constructor
  · intro h
    have hm : k*align<m*align := by omega
    have hk : k<m := (mul_lt_mul_right positive).mp hm
    have hkm : (k+1)*align≤m*align := Nat.mul_le_mul_right align hk
    rw [Nat.add_mul,Nat.one_mul] at hkm
    omega
  · intro h
    have hm : 0<m := by
      by_contra hn
      have : m=0 := by omega
      simp only [this,Nat.zero_mul] at target
      omega
    have ha : align≤m*align := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right align hm
    omega

theorem same_alignment (size1 size2 : Usize) (align : core.ptr.alignment.Alignment) :
    (core.alloc.layout.Layout.mk size1 align).align=
      (core.alloc.layout.Layout.mk size2 align).align := rfl

theorem product_error (product wordMax byteBound : Nat) (h : byteBound≤wordMax) :
    (product>wordMax ∨ product>byteBound) ↔ product>byteBound := by omega

theorem wrapped_available (capacity len size : Nat)
    (fits : len≤capacity) (bounded : capacity<size) :
    (capacity+size-len)%size=capacity-len := by
  have h : capacity+size-len=(capacity-len)+size := by omega
  rw [h,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

#print axioms product_error
#print axioms wrapped_available
#print axioms aligned_limit
#print axioms same_alignment
end R1Z.PV_FXM_ReserveLayout
