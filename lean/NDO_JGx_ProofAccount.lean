import RPz8_JFx_NativeBytes
import Aeneas
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_ProofAccount
open Aeneas Aeneas.Std Result

theorem proof_length : JFx_NativeBytes.proof.val.length=57607 := JFx_NativeBytes.proofBytes_length
#print axioms proof_length
attribute [local irreducible] JFx_NativeBytes.proof

def value (headerBytes : Array U8 688#usize) : Slice U8 :=
  ⟨headerBytes.val++JFx_NativeBytes.proof.val,by
    rw [List.length_append,headerBytes.property,proof_length]
    scalar_tac⟩

theorem length (headerBytes : Array U8 688#usize) : (value headerBytes).length=58295 := by
  change (headerBytes.val++JFx_NativeBytes.proof.val).length=58295
  rw [List.length_append,headerBytes.property,proof_length]
  rfl
#print axioms length

theorem suffix (headerBytes : Array U8 688#usize) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (value headerBytes) {start:=688#usize,«end»:=58295#usize}=ok JFx_NativeBytes.proof := by
  obtain ⟨out,run,contents,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨688#usize,58295#usize⟩ : core.ops.range.Range Usize) (value headerBytes)
      (by decide) (by rw [length];decide))
  have same : out=JFx_NativeBytes.proof := by
    apply Subtype.ext
    rw [contents]
    change ((headerBytes.val++JFx_NativeBytes.proof.val).drop 688).take 57607=_
    have hlen : headerBytes.val.length=688 := headerBytes.property
    have dropped : (headerBytes.val++JFx_NativeBytes.proof.val).drop 688=JFx_NativeBytes.proof.val := by
      have h : (headerBytes.val++JFx_NativeBytes.proof.val).drop headerBytes.val.length=JFx_NativeBytes.proof.val := List.drop_left
      simpa only [hlen] using h
    rw [dropped,List.take_of_length_le (by rw [proof_length])]

  exact run.trans (congrArg ok same)
#print axioms suffix
end AspisR1.JGx_ProofAccount
end
