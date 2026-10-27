import FIy_DigestLane
import FIw_PublicModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestRead
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
theorem value (d : Array U32 8#usize) (j : Fin 8) :
    (FIy_DigestLane.target d false j.val : K)=FIw_PublicModel.digest d j := by
  unfold FIy_DigestLane.target FIy_DigestTarget.value
  rw [if_neg (by simp)]
  unfold FIw_PublicModel.digest
  rw [List.getElem?_eq_getElem (by rw [d.property];exact j.isLt)]
  rfl
#print axioms value
end AspisR1.FIz_DigestRead
end
