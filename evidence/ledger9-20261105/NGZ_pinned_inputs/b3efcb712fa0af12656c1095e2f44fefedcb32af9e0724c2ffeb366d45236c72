import Lean
import NGE_NEQ_LateBorrow
import NGE_NEM_ArraySnapshotView

set_option autoImplicit false
noncomputable section
namespace NGE_NEQ_RootFrame
open Aeneas Aeneas.Std Result

theorem cover (post : Slice U8) (size : post.length = 1520) :
    ∃ array : Array U8 1520#usize, array.to_slice = post := by
  refine ⟨⟨post.val,size⟩,?_⟩
  apply Subtype.ext
  rfl

/-- Every earlier header copy preserves the SAME child's initial window. -/
theorem header_frame (src before : Nat → Option U8) (start width j : Nat)
    (ends : start+width ≤ 144) (later : 144 ≤ j) :
    KMX_CopyMeaning.loop src before start width j = before j := by
  rw [KMX_CopyMeaning.loop_spec]
  rw [if_neg (by omega)]

theorem scalar_frame (before : Nat → Option U8) (value : U8) (start j : Nat)
    (earlier : start < 144) (later : 144 ≤ j) :
    (if j=start then some value else before j) = before j := by
  rw [if_neg (by omega)]

/-- The entire arbitrary late poststate precedes one disjoint payment window. -/
theorem finish (before : Nat → Option U8) (late : Array U8 1520#usize)
    (pay : Array U8 216#usize) (j : Nat) :
    KMX_CopyMeaning.loop (fun k => pay.val[k-1664]?)
      (fun k => if 144 ≤ k ∧ k < 1664 then late.val[k-144]? else before k)
      1664 216 j =
      if 1664 ≤ j ∧ j < 1880 then pay.val[j-1664]?
      else if 144 ≤ j ∧ j < 1664 then late.val[j-144]? else before j := by
  rw [KMX_CopyMeaning.loop_spec]

/-- Complete successful bytes are the same three contiguous source regions. -/
theorem assembled (headBytes : List U8) (plen : headBytes.length = 144)
    (late : Array U8 1520#usize) (pay : Array U8 216#usize)
    (j : Nat) (bound : j < 1880) :
    KMX_CopyMeaning.loop (fun k => pay.val[k-1664]?)
      (fun k => if 144 ≤ k ∧ k < 1664 then late.val[k-144]? else headBytes[k]?)
      1664 216 j = ((headBytes ++ late.val) ++ pay.val)[j]? := by
  rw [finish]
  have llen : late.val.length = 1520 := late.property
  have total : (headBytes ++ late.val).length = 1664 := by
    rw [List.length_append,plen,llen]
  by_cases first : j < 144
  · rw [if_neg (by omega),if_neg (by omega)]
    rw [List.getElem?_append_left (by omega),List.getElem?_append_left (by omega)]
  · by_cases middle : j < 1664
    · rw [if_neg (by omega),if_pos (by omega)]
      rw [List.getElem?_append_left (by omega),List.getElem?_append_right (by omega),plen]
    · rw [if_pos (by omega),List.getElem?_append_right (by omega),total]

/-- Pointwise arbitrary-index observations identify the complete typed result. -/
theorem array_ext (a b : Array U8 1880#usize)
    (same : ∀ j : Nat, a.val[j]? = b.val[j]?) : a = b := by
  apply Subtype.ext
  exact List.ext_getElem? same

#print axioms cover
#print axioms header_frame
#print axioms scalar_frame
#print axioms finish
#print axioms assembled
#print axioms array_ext
end NGE_NEQ_RootFrame

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
