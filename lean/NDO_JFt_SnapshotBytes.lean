import NDO_JFt_Index
import NDO_JFt_SnapshotHeader
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotBytes
open Aeneas Aeneas.Std Result

theorem b8 : Slice.index_usize JFu_PublicRange.snapshot 8#usize=ok 1#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[8]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[8]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 8<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 8<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b9 : Slice.index_usize JFu_PublicRange.snapshot 9#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[9]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[9]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 9<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 9<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b10 : Slice.index_usize JFu_PublicRange.snapshot 10#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[10]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[10]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 10<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 10<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b11 : Slice.index_usize JFu_PublicRange.snapshot 11#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[11]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[11]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 11<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 11<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b12 : Slice.index_usize JFu_PublicRange.snapshot 12#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[12]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[12]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 12<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 12<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b13 : Slice.index_usize JFu_PublicRange.snapshot 13#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[13]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[13]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 13<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 13<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b14 : Slice.index_usize JFu_PublicRange.snapshot 14#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[14]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[14]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 14<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 14<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b15 : Slice.index_usize JFu_PublicRange.snapshot 15#usize=ok 0#u8 := by
  apply JFt_Index.source _ _ (by rw [JFu_PublicRange.snapshot,JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[15]?) JFu_PublicMeta01.selected
  change ((JFx_NativeBytes.publicInput.val.drop 176).take 800)[15]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 15<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 15<48),JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

#print axioms b8
#print axioms b9
#print axioms b10
#print axioms b11
#print axioms b12
#print axioms b13
#print axioms b14
#print axioms b15
end AspisR1.JFt_SnapshotBytes
