import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailPrefixFrameV7
open Aeneas Aeneas.Std

theorem range_back_prefix {α : Type} {n : Usize}
    (base : Array α n) (source : Slice α) (back : Slice α → Array α n)
    (start j : Nat)
    (hback : ∀ s, (back s).val = base.val.setSlice! start s.val)
    (hj : j < start) :
    (back source).val[j]? = base.val[j]? := by
  rw [hback source]
  exact List.setSlice!_getElem?_prefix base.val source.val start j hj

#print axioms range_back_prefix
end AspisR1PairForestLaneEncoderTailPrefixFrameV7
