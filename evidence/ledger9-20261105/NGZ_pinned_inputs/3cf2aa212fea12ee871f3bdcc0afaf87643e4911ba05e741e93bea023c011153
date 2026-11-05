import Lean
import NFY_Part031
import NFY_Part055

set_option autoImplicit false
noncomputable section
namespace NGE_NEJ_ConcreteFrame
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

/-- Fixed-array child return widths discharge every copy-window length. -/
theorem array_copy_frame {N W : Usize} (dst : Array U8 N) (src : Array U8 W)
    (start k : Nat) (fits : start + W.val ≤ N.val)
    (outside : k < start ∨ start + W.val ≤ k) :
    (dst.setSlice! start src.val).val[k]? = dst.val[k]? := by
  apply NFY_NEJ_ArrayFrame.array_frame
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
    (NFY_NBP_CommonBytes.encoded out magic kind c).val[k]? = out.val[k]? := by
  simp only [NFY_NBP_CommonBytes.encoded, NFY_NBP_CommonTail0.expected,
    NFY_NBP_CommonTail1.expected, NFY_NBP_CommonTail2.expected, NFY_NBP_CommonTail3.expected,
    NFY_NBP_CommonTail4.expected, NFY_NBP_CommonTail5.expected, NFY_NBP_CommonTail6.expected]
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
end NGE_NEJ_ConcreteFrame

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
