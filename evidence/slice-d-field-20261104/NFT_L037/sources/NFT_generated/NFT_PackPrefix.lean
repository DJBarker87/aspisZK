import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_PackPrefix
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedMaskQmPackBase4InitCopy

/-- General short-input copy law, without equating an initializer with a typeclass default. -/
theorem source {α : Type} (init : α) (copyInst : core.marker.Copy α)
    (values : Slice α) (short : values.length≤4) :
    ∃ out : Array α 4#usize, copyPrefixWith init copyInst values=ok out ∧
      out.val=values.val ++ List.replicate (4-values.length) init := by
  let padded : Array α 4#usize := Array.repeat 4#usize init
  let range : core.ops.range.RangeTo Usize := ⟨Slice.len values⟩
  have range_val : range.end.val=values.length := by simp [range,Slice.len_val]
  have opened := Array.index_mut_SliceIndexRangeToUsizeSlice padded range (by simpa [range_val] using short)
  obtain ⟨pair,run,post⟩:=WP.spec_imp_exists opened
  rcases pair with ⟨selected,back⟩
  have len : selected.length=values.length := by simpa [range_val] using post.2.1
  obtain ⟨copied,copyrun,copyval⟩:=WP.spec_imp_exists
    (core.slice.Slice.copy_from_slice.step_spec copyInst selected values len)
  refine ⟨back copied,?_,?_⟩
  · simp only [copyPrefixWith,padded,range,run,copyrun,bind_tc_ok]
  · rw [copyval,post.2.2 values]
    simp [padded,Array.repeat,List.setSlice!,List.slice,Nat.min_eq_left short]

#print axioms source
end NFT_PackPrefix
