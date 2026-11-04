import Lean
import NFY_Part032

set_option autoImplicit false
noncomputable section
namespace NGE_NEQ_LateBorrow
open Aeneas Aeneas.Std Result

/-- The actual emitted borrow and its back function, on the same allocation.
The poststate is arbitrary: this is not a one-cell mutation restriction. -/
theorem rejoin (out : Slice U8) (size : out.length = 1880) :
    ∃ child back,
      core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice U8)
        out {start := 144#usize, «end» := 1664#usize} = ok (child,back) ∧
      child.length = 1520 ∧ ∀ post : Slice U8, back post = out.setSlice! 144 post.val := by
  have guard : (144#usize) ≤ 1664#usize ∧ (1664#usize).val ≤ out.length := by
    constructor
    · decide
    · rw [size]; decide
  simp only [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,if_pos guard]
  refine ⟨_,_,rfl,?_,?_⟩
  · have len : out.val.length = 1880 := size
    simp only [Slice.length,List.slice,List.length_take,List.length_drop,len]
    decide
  · intro post
    rfl

/-- All possible 1520-byte child poststates and every external allocation byte. -/
theorem poststate (out post : Slice U8) (size : out.length = 1880)
    (post_size : post.length = 1520) (k : Nat) :
    (out.setSlice! 144 post.val).val[k]? =
      if 144 ≤ k ∧ k < 1664 then post.val[k-144]? else out.val[k]? := by
  rw [← NFY_NEL_SliceCopyLaw.loop_binding out post 144 k (by rw [post_size,size]; decide)]
  rw [KMX_CopyMeaning.loop_spec,post_size]

/-- The later afterstate write preserves the exact child's whole poststate. -/
theorem after_preserves_child (out post : Slice U8) (size : out.length = 1880)
    (after : Array U8 216#usize) (k : Nat) (earlier : k < 1664) :
    ((out.setSlice! 144 post.val).setSlice! 1664 after.val).val[k]? =
      (out.setSlice! 144 post.val).val[k]? := by
  apply NFY_NEJ_ArrayFrame.list_frame
  · have len : out.val.length = 1880 := size
    simp only [Slice.setSlice!,List.length_setSlice!,after.property,len]
    decide
  · exact Or.inl earlier

#print axioms rejoin
#print axioms poststate
#print axioms after_preserves_child
end NGE_NEQ_LateBorrow

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
