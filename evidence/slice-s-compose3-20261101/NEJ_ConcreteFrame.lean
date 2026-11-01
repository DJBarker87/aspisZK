import NEJ_ArrayFrame
import NED_CommonEncodeCohort
set_option autoImplicit false
noncomputable section
namespace NEJ_ConcreteFrame
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Fixed-array child return widths discharge every copy-window length. -/
theorem array_copy_frame {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val)
    (outside : k < start ∨ start + W.val ≤ k) :
    (dst.setSlice! start src.val).val[k]? = dst.val[k]? := by
  apply NEJ_ArrayFrame.array_frame
  · simpa only [src.property] using fits
  · simpa only [src.property] using outside

theorem scalar_frame {N : Usize} (dst : Array U8 N) (i : Usize) (v : U8) (k : Nat)
    (different : k ≠ i.val) : (dst.set i v).val[k]? = dst.val[k]? := by
  change (dst.val.set i.val v)[k]? = dst.val[k]?
  exact List.getElem?_set_ne different.symm

/-- All emitted field writes preserve the original reserved byte/suffix.
This theorem quantifies over arbitrary common fields and arbitrary prestate. -/
theorem encoded_frame (out : Array U8 216#usize) (magic : Array U8 4#usize)
    (kind : pool_v1.historical_anchor.PoolV1TransitionKind)
    (c : pool_v1.payment_relation.CommonPublicV1) (k : Nat)
    (outside : k = 7 ∨ 148 ≤ k) :
    (NBP_CommonBytes.encoded out magic kind c).val[k]? = out.val[k]? := by
  simp only [NBP_CommonBytes.encoded, NBP_CommonTail0.expected,
    NBP_CommonTail1.expected, NBP_CommonTail2.expected, NBP_CommonTail3.expected,
    NBP_CommonTail4.expected, NBP_CommonTail5.expected, NBP_CommonTail6.expected]
  rw [array_copy_frame _ _ 144 k (by decide) (by scalar_tac)]
  rw [array_copy_frame _ _ 112 k (by decide) (by scalar_tac)]
  rw [array_copy_frame _ _ 80 k (by decide) (by scalar_tac)]
  rw [array_copy_frame _ _ 72 k (by decide) (by scalar_tac)]
  rw [array_copy_frame _ _ 40 k (by decide) (by scalar_tac)]
  rw [array_copy_frame _ _ 8 k (by decide) (by scalar_tac)]
  rw [scalar_frame _ _ _ k (by scalar_tac)]
  rw [scalar_frame _ _ _ k (by scalar_tac)]
  rw [scalar_frame _ _ _ k (by scalar_tac)]
  exact array_copy_frame out magic 0 k (by decide) (by scalar_tac)

#print axioms array_copy_frame
#print axioms scalar_frame
#print axioms encoded_frame
end NEJ_ConcreteFrame
