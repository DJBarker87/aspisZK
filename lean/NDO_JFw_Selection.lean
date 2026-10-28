import NDO_JFw_RealExpansion
set_option autoImplicit false
namespace AspisR1.JFw_Selection
open Aeneas Aeneas.Std Result

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JFx_NativeBytes.proof {start:=16#usize,«end»:=7031#usize} = ok JFw_RealExpansion.stored := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  have length : JFx_NativeBytes.proof.length = 57607 := JFx_NativeBytes.proofBytes_length
  have fits : 16#usize ≤ 7031#usize ∧ (7031#usize).val ≤ JFx_NativeBytes.proof.length := by
    rw [length];scalar_tac
  rw [if_pos fits]
  apply congrArg Result.ok
  apply Subtype.ext
  change List.slice (16#usize).val (7031#usize).val JFx_NativeBytes.proof.val =
    (JFx_NativeBytes.proof.val.drop 16).take 7015
  simp only [List.slice,show (16#usize).val=16 from rfl,show (7031#usize).val=7031 from rfl]

#print axioms source
end AspisR1.JFw_Selection
