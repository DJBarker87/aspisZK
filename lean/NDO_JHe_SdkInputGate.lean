import NDO_JHe_Natives
import NDO_JHb_Header
import NDO_JFs_PrefixRead
import NDO_JFt_Index
import S2SdkProofComparatorV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_SdkInputGate
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHb_Header.value

theorem headerPrefix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    JHb_Header.account {«end»:=688#usize}=ok JHb_Header.value.to_slice := by
  apply JFs_PrefixRead.source _ _ (by rw [JHb_Header.length];decide)
  change (JHb_Header.value.val++JFx_NativeBytes.proof.val).take 688=JHb_Header.value.val
  have take : (JHb_Header.value.val++JFx_NativeBytes.proof.val).take JHb_Header.value.val.length=JHb_Header.value.val := List.take_left
  have len : JHb_Header.value.val.length=688 := JHb_Header.value.property
  rw [len] at take
  exact take
#print axioms headerPrefix

theorem comparison (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (JHe_Natives.sdk base stage).op0 core.cmp.PartialEqU8 JHb_Header.value.to_slice JHb_Header.value=ok false := by
  change core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8
    JHb_Header.value.to_slice JHb_Header.value.to_slice=ok false
  rw [AspisS2OwnedStage1.SdkReference.ProofGate.standard_ne]
  simp only [ne_self_iff_false,decide_false]
#print axioms comparison

theorem instruction (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    (JHe_Natives.sdk base stage).op1 core.cmp.PartialEqU8 JHe_Natives.data1
      (Array.make 2#usize [3#u8,10#u8])=ok true := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8
    JHe_Natives.data1 (Array.make 2#usize [3#u8,10#u8]).to_slice=ok true
  rfl
#print axioms instruction

theorem proof_tag : JFx_NativeBytes.proof.val[8]?=some 2#u8 := by rfl
#print axioms proof_tag

theorem tag : Slice.index_usize JHb_Header.account 696#usize=ok 2#u8 := by
  apply JFt_Index.source _ _ (by rw [JHb_Header.length];decide)
  change (JHb_Header.value.val++JFx_NativeBytes.proof.val)[696]?=some 2#u8
  rw [List.getElem?_append_right (by rw [JHb_Header.value.property];decide)]
  rw [JHb_Header.value.property]
  exact proof_tag
#print axioms tag
end AspisR1.JHe_SdkInputGate
end
