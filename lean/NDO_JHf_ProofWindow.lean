import NDO_JHb_Header
import NDO_JFx_NativeHeader
import NDO_JFt_Index
set_option autoImplicit false
namespace AspisR1.JHf_ProofWindow
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JHb_Header.value JHb_Header.account

theorem first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    JHb_Header.account {start:=0#usize,«end»:=688#usize}=ok JHb_Header.value.to_slice := by
  obtain ⟨out,run,contents,size⟩:=WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨0#usize,688#usize⟩ : core.ops.range.Range Usize) JHb_Header.account
      (by decide) (by rw [JHb_Header.length];decide))
  have same : out=JHb_Header.value.to_slice := by
    apply Subtype.ext
    rw [contents]
    simp only [List.slice,JHb_Header.account,JGx_ProofAccount.value,
      show (0#usize).val=0 from rfl,show (688#usize).val=688 from rfl,
      Nat.sub_zero,List.drop_zero,List.take_append,
      JHb_Header.value.property,Array.to_slice,Nat.sub_self,List.take_zero,List.append_nil,
      List.take_length]
    exact List.take_of_length_le (by rw [JHb_Header.value.property];exact Nat.le_refl 688)
  exact run.trans (congrArg ok same)
#print axioms first

theorem proof_tag : JFx_NativeBytes.proof.val[8]?=some 2#u8 := by
  have h:=congrArg (fun xs : List U8=>xs[8]?) JFx_NativeHeader.first_sixteen
  rw [List.getElem?_take_of_lt (by decide : 8<16)] at h
  exact h
#print axioms proof_tag

theorem tag : Slice.index_usize JHb_Header.account 696#usize=ok 2#u8 := by
  apply JFt_Index.source _ _ (by rw [JHb_Header.length];decide) 2#u8
  simp only [JHb_Header.account,JGx_ProofAccount.value,List.getElem?_append,
    JHb_Header.value.property,show (696#usize).val=696 from rfl]
  exact proof_tag
#print axioms tag
end AspisR1.JHf_ProofWindow
