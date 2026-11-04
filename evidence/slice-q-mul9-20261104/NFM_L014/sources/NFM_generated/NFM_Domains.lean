import NFM_Control
import NFI_WrapperDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFM_Domains
open Aeneas Aeneas.Std Result

/-- The host window's incoming limb cap is derived from the actual outer
invariant at each fixed position, never an independent successful packet. -/
theorem limb_cap (limbs : Array U64 8#usize) (k : Fin 7)
    (bound : NFE_NFA_FoldEight.Bound limbs k.val)
    (word : U64) (member : word∈limbs.val) :
    word.val≤6*10737418238 := by
  have h:=bound word member
  have cap:=Nat.mul_le_mul_right NFE_NFA_FoldLane.R (show k.val≤6 by omega)
  change word.val≤k.val*NFE_NFA_FoldLane.R at h
  exact h.trans cap

/-- The frozen reset supplies the native window precondition even in the
short final window, which permits but does not require extra headroom. -/
theorem sums_reset (width : Nat) (small : width≤4) :
    (0 : Nat)≤(4-width)*NEG_DotDomain.B := Nat.zero_le _

theorem slots : ∀ slot∈([0,1,2,3] : List Nat),slot<4 := by decide

#print axioms limb_cap
#print axioms sums_reset
#print axioms slots
end AspisR1.NFM_Domains
end
