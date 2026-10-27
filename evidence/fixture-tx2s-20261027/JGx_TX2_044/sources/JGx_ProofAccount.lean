import JFx_NativeBytes
import Aeneas
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_ProofAccount
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof

def value (prefix : Array U8 688#usize) : Slice U8 :=
  ⟨prefix.val++JFx_NativeBytes.proof.val,by
    rw [List.length_append,prefix.property,JFx_NativeBytes.proofBytes_length]
    scalar_tac⟩

theorem length (prefix : Array U8 688#usize) : (value prefix).length=58295 := by
  change (prefix.val++JFx_NativeBytes.proof.val).length=58295
  rw [List.length_append,prefix.property,JFx_NativeBytes.proofBytes_length]
#print axioms length

theorem suffix (prefix : Array U8 688#usize) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (value prefix) {start:=688#usize,«end»:=58295#usize}=ok JFx_NativeBytes.proof := by
  obtain ⟨out,run,contents,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨688#usize,58295#usize⟩ : core.ops.range.Range Usize) (value prefix)
      (by decide) (by rw [length];decide))
  have same : out=JFx_NativeBytes.proof := by
    apply Subtype.ext
    rw [contents]
    change ((prefix.val++JFx_NativeBytes.proof.val).drop 688).take (58295-688)=_
    rw [List.drop_append,prefix.property]
    simp only [show (688#usize).val=688 from rfl,Nat.sub_self,List.drop_eq_nil_of_le (by rw [prefix.property]),List.drop_zero,List.nil_append]
    rw [show 58295-688=57607 from by decide,List.take_of_length_le (by rw [JFx_NativeBytes.proofBytes_length])]
  exact run.trans (congrArg ok same)
#print axioms suffix
end AspisR1.JGx_ProofAccount
end
