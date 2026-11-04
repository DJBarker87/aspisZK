import Lean
import NFY_Part037
import NFY_Part038
import NFY_Part036
import RPz7_S6NativeSnapshotDecoderFactoredV1
import NFY_Part024
import NFY_Part023
import NFY_Part034
import NFY_Part022
import NFY_Part035
import NFY_Part020

-- BEGIN copied JFt_SnapshotValue: lean/JFt_SnapshotValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def value : PoolV1PairLiveSnapshotV1 :=
  {pool:=NFY_JFu_PublicBindings.pool,deployment_domain:=NFY_JFu_PublicBindings.domain,
   sequence:=13#u64,next_pair_index:=13#u64,current_root:=NFY_JFt_Digest01.value,
   frontier:=Array.make 20#usize [NFY_JFt_Digest02.value,NFY_JFt_Digest03.value,NFY_JFt_Digest04.value,NFY_JFt_Digest05.value,NFY_JFt_Digest06.value,NFY_JFt_Digest07.value,NFY_JFt_Digest08.value,NFY_JFt_Digest09.value,NFY_JFt_Digest10.value,NFY_JFt_Digest11.value,NFY_JFt_Digest12.value,NFY_JFt_Digest13.value,NFY_JFt_Digest14.value,NFY_JFt_Digest15.value,NFY_JFt_Digest16.value,NFY_JFt_Digest17.value,NFY_JFt_Digest18.value,NFY_JFt_Digest19.value,NFY_JFt_Digest20.value,NFY_JFt_Digest21.value]}

theorem frontier : ∀ i : Fin 20,AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment (336+32*i.val) 32 (by have h:=i.isLt;omega))=
    ok (.Ok (value.frontier.val[i.val]'(by simp only [value,Array.make];exact i.isLt))) := by
  intro i
  fin_cases i
  · exact NFY_JFt_Digest02.source
  · exact NFY_JFt_Digest03.source
  · exact NFY_JFt_Digest04.source
  · exact NFY_JFt_Digest05.source
  · exact NFY_JFt_Digest06.source
  · exact NFY_JFt_Digest07.source
  · exact NFY_JFt_Digest08.source
  · exact NFY_JFt_Digest09.source
  · exact NFY_JFt_Digest10.source
  · exact NFY_JFt_Digest11.source
  · exact NFY_JFt_Digest12.source
  · exact NFY_JFt_Digest13.source
  · exact NFY_JFt_Digest14.source
  · exact NFY_JFt_Digest15.source
  · exact NFY_JFt_Digest16.source
  · exact NFY_JFt_Digest17.source
  · exact NFY_JFt_Digest18.source
  · exact NFY_JFt_Digest19.source
  · exact NFY_JFt_Digest20.source
  · exact NFY_JFt_Digest21.source

theorem validated : validate_pool_v1_pair_live_snapshot_v1 value=ok (.Ok ()) :=
  NFY_JFt_SnapshotAcceptance.source value rfl rfl rfl rfl NFY_JFt_Digest01.source frontier

#print axioms frontier
#print axioms validated
end AspisR1.NFY_JFt_SnapshotValue
-- END copied JFt_SnapshotValue
-- BEGIN copied JFt_SnapshotTail: lean/JFt_SnapshotTail.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotTail
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_16 NFY_JFu_PublicRange.snapshot NFY_JFt_Digest01.value NFY_JFt_Digest02.value NFY_JFt_Digest03.value NFY_JFt_Digest04.value NFY_JFt_Digest05.value NFY_JFt_Digest06.value NFY_JFt_Digest07.value NFY_JFt_Digest08.value NFY_JFt_Digest09.value NFY_JFt_Digest10.value NFY_JFt_Digest11.value NFY_JFt_Digest12.value NFY_JFt_Digest13.value NFY_JFt_Digest14.value NFY_JFt_Digest15.value NFY_JFt_Digest16.value NFY_JFt_Digest17.value=ok (.Ok NFY_JFt_SnapshotValue.value) := by
  unfold part_16
  simp only [NFY_JFu_PublicRange.snapshot,
    show (48#usize).val=48 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (120#usize).val=120 from rfl,
    show (128#usize).val=128 from rfl,
    show (672#usize).val=672 from rfl,
    show (704#usize).val=704 from rfl,
    show (736#usize).val=736 from rfl,
    show (768#usize).val=768 from rfl,
    show (800#usize).val=800 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    NFY_JFt_Range.read 176 800 (by decide) 672#usize 704#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 704#usize 736#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 736#usize 768#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 768#usize 800#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 48#usize 80#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 80#usize 112#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 112#usize 120#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 120#usize 128#usize (by decide) (by decide),
    NFY_JFt_Digest18.source,
    NFY_JFt_Digest19.source,
    NFY_JFt_Digest20.source,
    NFY_JFt_Digest21.source,
    NFY_JFt_Metadata.pool,
    NFY_JFt_Metadata.domain,
    NFY_JFt_Metadata.sequence,
    NFY_JFt_Metadata.index,
    lift,bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    NFY_JFu_PublicIndices.sequence]
  have validated:=NFY_JFt_SnapshotValue.validated
  unfold NFY_JFt_SnapshotValue.value at validated
  rw [validated]
  rfl

#print axioms source
end AspisR1.NFY_JFt_SnapshotTail
-- END copied JFt_SnapshotTail
-- BEGIN copied JFt_Snapshot12: lean/JFt_Snapshot12.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Snapshot12
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_12 NFY_JFu_PublicRange.snapshot NFY_JFt_Digest01.value NFY_JFt_Digest02.value NFY_JFt_Digest03.value NFY_JFt_Digest04.value NFY_JFt_Digest05.value NFY_JFt_Digest06.value NFY_JFt_Digest07.value NFY_JFt_Digest08.value NFY_JFt_Digest09.value NFY_JFt_Digest10.value NFY_JFt_Digest11.value NFY_JFt_Digest12.value NFY_JFt_Digest13.value=ok (.Ok NFY_JFt_SnapshotValue.value) := by
  have tail:=NFY_JFt_SnapshotTail.source
  unfold NFY_JFu_PublicRange.snapshot at tail
  unfold part_12
  simp only [NFY_JFu_PublicRange.snapshot,
    show (544#usize).val=544 from rfl,
    show (576#usize).val=576 from rfl,
    show (608#usize).val=608 from rfl,
    show (640#usize).val=640 from rfl,
    show (672#usize).val=672 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    NFY_JFt_Range.read 176 800 (by decide) 544#usize 576#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 576#usize 608#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 608#usize 640#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 640#usize 672#usize (by decide) (by decide),
    NFY_JFt_Digest14.source,
    NFY_JFt_Digest15.source,
    NFY_JFt_Digest16.source,
    NFY_JFt_Digest17.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Snapshot12
-- END copied JFt_Snapshot12
-- BEGIN copied JFt_Snapshot08: lean/JFt_Snapshot08.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Snapshot08
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_8 NFY_JFu_PublicRange.snapshot NFY_JFt_Digest01.value NFY_JFt_Digest02.value NFY_JFt_Digest03.value NFY_JFt_Digest04.value NFY_JFt_Digest05.value NFY_JFt_Digest06.value NFY_JFt_Digest07.value NFY_JFt_Digest08.value NFY_JFt_Digest09.value=ok (.Ok NFY_JFt_SnapshotValue.value) := by
  have tail:=NFY_JFt_Snapshot12.source
  unfold NFY_JFu_PublicRange.snapshot at tail
  unfold part_8
  simp only [NFY_JFu_PublicRange.snapshot,
    show (416#usize).val=416 from rfl,
    show (448#usize).val=448 from rfl,
    show (480#usize).val=480 from rfl,
    show (512#usize).val=512 from rfl,
    show (544#usize).val=544 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    NFY_JFt_Range.read 176 800 (by decide) 416#usize 448#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 448#usize 480#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 480#usize 512#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 512#usize 544#usize (by decide) (by decide),
    NFY_JFt_Digest10.source,
    NFY_JFt_Digest11.source,
    NFY_JFt_Digest12.source,
    NFY_JFt_Digest13.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Snapshot08
-- END copied JFt_Snapshot08
-- BEGIN copied JFt_Snapshot04: lean/JFt_Snapshot04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Snapshot04
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_4 NFY_JFu_PublicRange.snapshot NFY_JFt_Digest01.value NFY_JFt_Digest02.value NFY_JFt_Digest03.value NFY_JFt_Digest04.value NFY_JFt_Digest05.value=ok (.Ok NFY_JFt_SnapshotValue.value) := by
  have tail:=NFY_JFt_Snapshot08.source
  unfold NFY_JFu_PublicRange.snapshot at tail
  unfold part_4
  simp only [NFY_JFu_PublicRange.snapshot,
    show (288#usize).val=288 from rfl,
    show (320#usize).val=320 from rfl,
    show (352#usize).val=352 from rfl,
    show (384#usize).val=384 from rfl,
    show (416#usize).val=416 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    NFY_JFt_Range.read 176 800 (by decide) 288#usize 320#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 320#usize 352#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 352#usize 384#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 384#usize 416#usize (by decide) (by decide),
    NFY_JFt_Digest06.source,
    NFY_JFt_Digest07.source,
    NFY_JFt_Digest08.source,
    NFY_JFt_Digest09.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Snapshot04
-- END copied JFt_Snapshot04
-- BEGIN copied JFt_Snapshot00: lean/JFt_Snapshot00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Snapshot00
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_0 NFY_JFu_PublicRange.snapshot NFY_JFt_Digest01.value=ok (.Ok NFY_JFt_SnapshotValue.value) := by
  have tail:=NFY_JFt_Snapshot04.source
  unfold NFY_JFu_PublicRange.snapshot at tail
  unfold part_0
  simp only [NFY_JFu_PublicRange.snapshot,
    show (160#usize).val=160 from rfl,
    show (192#usize).val=192 from rfl,
    show (224#usize).val=224 from rfl,
    show (256#usize).val=256 from rfl,
    show (288#usize).val=288 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    NFY_JFt_Range.read 176 800 (by decide) 160#usize 192#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 192#usize 224#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 224#usize 256#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 256#usize 288#usize (by decide) (by decide),
    NFY_JFt_Digest02.source,
    NFY_JFt_Digest03.source,
    NFY_JFt_Digest04.source,
    NFY_JFt_Digest05.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.NFY_JFt_Snapshot00
-- END copied JFt_Snapshot00
-- BEGIN copied JFt_SnapshotBytes: lean/JFt_SnapshotBytes.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotBytes
open Aeneas Aeneas.Std Result

theorem b8 : Slice.index_usize NFY_JFu_PublicRange.snapshot 8#usize=ok 1#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 1#u8
  have h:=congrArg (fun xs : List U8 => xs[8]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[8]?=some 1#u8
  rw [List.getElem?_take_of_lt (by decide : 8<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 8<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b9 : Slice.index_usize NFY_JFu_PublicRange.snapshot 9#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[9]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[9]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 9<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 9<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b10 : Slice.index_usize NFY_JFu_PublicRange.snapshot 10#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[10]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[10]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 10<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 10<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b11 : Slice.index_usize NFY_JFu_PublicRange.snapshot 11#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[11]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[11]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 11<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 11<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b12 : Slice.index_usize NFY_JFu_PublicRange.snapshot 12#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[12]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[12]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 12<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 12<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b13 : Slice.index_usize NFY_JFu_PublicRange.snapshot 13#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[13]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[13]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 13<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 13<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b14 : Slice.index_usize NFY_JFu_PublicRange.snapshot 14#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[14]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[14]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 14<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 14<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

theorem b15 : Slice.index_usize NFY_JFu_PublicRange.snapshot 15#usize=ok 0#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.snapshot,NFY_JFu_PublicRange.length];decide) 0#u8
  have h:=congrArg (fun xs : List U8 => xs[15]?) NFY_JFu_PublicMeta01.selected
  change ((NFY_JFx_NativeBytes.publicInput.val.drop 176).take 800)[15]?=some 0#u8
  rw [List.getElem?_take_of_lt (by decide : 15<800)]
  simpa only [List.getElem?_take_of_lt (by decide : 15<48),NFY_JFu_PublicMeta01.bytes,
    List.getElem?_cons_succ,List.getElem?_cons_zero] using h

#print axioms b8
#print axioms b9
#print axioms b10
#print axioms b11
#print axioms b12
#print axioms b13
#print axioms b14
#print axioms b15
end AspisR1.NFY_JFt_SnapshotBytes
-- END copied JFt_SnapshotBytes
-- BEGIN copied JFt_SnapshotDecode: lean/JFt_SnapshotDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem factored : AspisS6NativeSnapshotDecoderFactored.decode NFY_JFu_PublicRange.snapshot=
    ok (.Ok NFY_JFt_SnapshotValue.value) := by
  have size : Slice.len NFY_JFu_PublicRange.snapshot=800#usize := by
    have h : NFY_JFu_PublicRange.snapshot.length=800 := NFY_JFu_PublicRange.length 176 800 (by decide)
    scalar_tac
  have lengthCheck : (800#usize !=800#usize)=false := by decide
  have oneCheck : (1#u8 !=1#u8)=false := by decide
  have zeroCheck : (0#u8 !=0#u8)=false := by decide
  have b8:=NFY_JFt_SnapshotBytes.b8
  unfold NFY_JFu_PublicRange.snapshot at b8
  have b9:=NFY_JFt_SnapshotBytes.b9
  unfold NFY_JFu_PublicRange.snapshot at b9
  have b10:=NFY_JFt_SnapshotBytes.b10
  unfold NFY_JFu_PublicRange.snapshot at b10
  have b11:=NFY_JFt_SnapshotBytes.b11
  unfold NFY_JFu_PublicRange.snapshot at b11
  have b12:=NFY_JFt_SnapshotBytes.b12
  unfold NFY_JFu_PublicRange.snapshot at b12
  have b13:=NFY_JFt_SnapshotBytes.b13
  unfold NFY_JFu_PublicRange.snapshot at b13
  have b14:=NFY_JFt_SnapshotBytes.b14
  unfold NFY_JFu_PublicRange.snapshot at b14
  have b15:=NFY_JFt_SnapshotBytes.b15
  unfold NFY_JFu_PublicRange.snapshot at b15
  have tail:=NFY_JFt_Snapshot00.source
  unfold NFY_JFu_PublicRange.snapshot at tail
  unfold AspisS6NativeSnapshotDecoderFactored.decode
  simp only [size,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,lengthCheck,oneCheck,zeroCheck,Bool.false_eq_true,↓reduceIte]
  simp only [NFY_JFu_PublicRange.snapshot,
    NFY_JFt_LocalWindow.firstn 176 800 8#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,NFY_JFt_SnapshotHeader.magic_selected,
    NFY_JFt_SnapshotConstants.magic_array,bind_tc_ok,NFY_JFt_SnapshotConstants.magic_compare]
  simp only [b8,b9,
    b10,b11,b12,b13,
    b14,b15,bind_tc_ok,
    POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION,lengthCheck,oneCheck,zeroCheck,Bool.false_eq_true,↓reduceIte]
  simp only [NFY_JFu_PublicRange.snapshot,
    NFY_JFt_Range.read 176 800 (by decide) 16#usize 48#usize (by decide) (by decide),
    NFY_JFt_Range.read 176 800 (by decide) 128#usize 160#usize (by decide) (by decide),
    show (16#usize).val=16 from rfl,show (48#usize).val=48 from rfl,
    show (128#usize).val=128 from rfl,show (160#usize).val=160 from rfl,Nat.reduceAdd,Nat.reduceSub,
    NFY_JFt_SnapshotHeader.format_selected,NFY_JFt_SnapshotConstants.format_call,
    NFY_JFt_SnapshotConstants.format_array,NFY_JFt_SnapshotConstants.format_compare,
    NFY_JFt_Digest01.source,bind_tc_ok,AspisR1TerminalDecoder.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    Bool.false_eq_true,↓reduceIte,tail]

theorem source : decode_pool_v1_pair_live_snapshot_v1 NFY_JFu_PublicRange.snapshot=
    ok (.Ok NFY_JFt_SnapshotValue.value) :=
  (AspisS6NativeSnapshotDecoderFactored.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.NFY_JFt_SnapshotDecode
-- END copied JFt_SnapshotDecode
-- BEGIN copied JFs_LateChildren: lean/JFs_LateChildren.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateChildren
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def value : PoolV1PairLatePublicStatementV1 :=
  ⟨NFY_JFt_SnapshotValue.value,NFY_JFt_AfterstateValue.value⟩

theorem snapshot : decode_pair_live_snapshot_boxed_v1 NFY_JFu_PublicRange.snapshot=
    ok (.Ok NFY_JFt_SnapshotValue.value) := by
  unfold decode_pair_live_snapshot_boxed_v1
  rw [NFY_JFt_SnapshotDecode.source]
  rfl

theorem afterstate : decode_pair_afterstate_boxed_v1 NFY_JFu_PublicRange.afterstate=
    ok (.Ok NFY_JFt_AfterstateValue.value) := by
  unfold decode_pair_afterstate_boxed_v1
  rw [NFY_JFs_AfterstateDecode.source]
  rfl

theorem next : U64.checked_add NFY_JFt_SnapshotValue.value.next_pair_index 1#u64=
    some NFY_JFt_AfterstateValue.value.next_pair_index := by rfl

theorem next_compare : core.cmp.PartialEq.ne.trait_default
    (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64)
    (some NFY_JFt_AfterstateValue.value.next_pair_index)
    (some NFY_JFt_AfterstateValue.value.next_pair_index)=ok false := by rfl

#print axioms snapshot
#print axioms afterstate
#print axioms next
#print axioms next_compare
end AspisR1.NFY_JFs_LateChildren
-- END copied JFs_LateChildren
-- BEGIN copied JFs_RangeFrom: lean/JFs_RangeFrom.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_RangeFrom
open Aeneas Aeneas.Std Result WP

theorem read (off n : Nat) (bound : off+n≤1880) (start : Usize) (inside : start.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {start:=start}=
      ok (NFY_JFu_PublicRange.segment (off+start.val) (n-start.val) (by omega)) := by
  have size:=NFY_JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {start:=start}
      ⦃ out => out=NFY_JFu_PublicRange.segment (off+start.val) (n-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,NFY_JFu_PublicRange.segment,List.drop_take,List.drop_drop] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms read
end AspisR1.NFY_JFs_RangeFrom
-- END copied JFs_RangeFrom
-- BEGIN copied JFs_LateTail: lean/JFs_LateTail.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateTail
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem source : AspisS6NativeLateDecoderSplit.decode_tail NFY_JFu_PublicRange.late=
    ok (.Ok NFY_JFs_LateChildren.value) := by
  have b24:=NFY_JFs_LateBytes.b24
  have b25:=NFY_JFs_LateBytes.b25
  have b26:=NFY_JFs_LateBytes.b26
  have b27:=NFY_JFs_LateBytes.b27
  have b28:=NFY_JFs_LateBytes.b28
  have b29:=NFY_JFs_LateBytes.b29
  have b30:=NFY_JFs_LateBytes.b30
  have b31:=NFY_JFs_LateBytes.b31
  unfold NFY_JFu_PublicRange.late at b24 b25 b26 b27 b28 b29 b30 b31
  have zero : (0#u8 !=0#u8)=false := by decide
  obtain ⟨sum,add,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=32#usize) (y:=800#usize) (by scalar_tac))
  have same : sum=832#usize := by scalar_tac
  rw [same] at add
  have snapshot:=NFY_JFs_LateChildren.snapshot
  have afterstate:=NFY_JFs_LateChildren.afterstate
  unfold NFY_JFu_PublicRange.snapshot at snapshot
  unfold NFY_JFu_PublicRange.afterstate at afterstate
  unfold AspisS6NativeLateDecoderSplit.decode_tail
  simp only [NFY_JFu_PublicRange.late,b24,b25,b26,b27,b28,b29,b30,b31,bind_tc_ok,zero,
    Bool.false_eq_true,↓reduceIte,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,add]
  simp only [NFY_JFt_Range.read 144 1520 (by decide) 32#usize 832#usize (by decide) (by decide),
    NFY_JFs_RangeFrom.read 144 1520 (by decide) 832#usize (by decide),
    show (32#usize).val=32 from rfl,show (832#usize).val=832 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    snapshot,afterstate,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    NFY_JFs_LateChildren.next,lift,NFY_JFs_LateChildren.next_compare,
    Bool.false_eq_true,↓reduceIte]
  rfl

#print axioms source
end AspisR1.NFY_JFs_LateTail
-- END copied JFs_LateTail
-- BEGIN copied JFs_LateDecode: lean/JFs_LateDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem factored : AspisS6NativeLateDecoderSplit.decode NFY_JFu_PublicRange.late=
    ok (.Ok NFY_JFs_LateChildren.value) := by
  have tail:=NFY_JFs_LateTail.source
  unfold NFY_JFu_PublicRange.late at tail
  have b8:=NFY_JFs_LateBytes.b8
  have b9:=NFY_JFs_LateBytes.b9
  unfold NFY_JFu_PublicRange.late at b8 b9
  have one : (1#u8 !=1#u8)=false := by decide
  have two : (2#u8 !=2#u8)=false := by decide
  have lengthCheck : (1520#usize !=1520#usize)=false := by decide
  unfold AspisS6NativeLateDecoderSplit.decode
  simp only [NFY_JFs_LateConstants.length,NFY_JFs_LateConstants.size,bind_tc_ok,lengthCheck,
    Bool.false_eq_true,↓reduceIte]
  simp only [NFY_JFu_PublicRange.late,
    NFY_JFt_LocalWindow.firstn 144 1520 8#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,NFY_JFs_LateBytes.magic_selected,
    NFY_JFs_LateConstants.magic_array,NFY_JFs_LateConstants.magic_compare,bind_tc_ok,
    Bool.false_eq_true,↓reduceIte,b8,b9,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT,
    one,two]
  simp only [NFY_JFt_Range.read 144 1520 (by decide) 10#usize 12#usize (by decide) (by decide),
    NFY_JFt_Range.read 144 1520 (by decide) 12#usize 16#usize (by decide) (by decide),
    NFY_JFt_Range.read 144 1520 (by decide) 16#usize 20#usize (by decide) (by decide),
    NFY_JFt_Range.read 144 1520 (by decide) 20#usize 24#usize (by decide) (by decide),
    show (10#usize).val=10 from rfl,show (12#usize).val=12 from rfl,
    show (16#usize).val=16 from rfl,show (20#usize).val=20 from rfl,show (24#usize).val=24 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFs_LateWords.read10,NFY_JFs_LateWords.read12,NFY_JFs_LateWords.read16,NFY_JFs_LateWords.read20,
    NFY_JFs_LateWords.word10,NFY_JFs_LateWords.word12,NFY_JFs_LateWords.word16,NFY_JFs_LateWords.word20,
    NFY_JFs_LateWords.cast10,NFY_JFs_LateWords.cast12,NFY_JFs_LateWords.cast16,NFY_JFs_LateWords.cast20,
    lift,bind_tc_ok,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,
    NFY_JFs_AfterstateSize.bytes,show (32#usize !=32#usize)=false from by decide,
    show (800#usize !=800#usize)=false from by decide,
    show (688#usize !=688#usize)=false from by decide,lengthCheck,
    Bool.false_eq_true,↓reduceIte,tail]

theorem source : decode_pool_v1_pair_late_public_statement_boxed_v1 NFY_JFu_PublicRange.late=
    ok (.Ok NFY_JFs_LateChildren.value) :=
  (AspisS6NativeLateDecoderSplit.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.NFY_JFs_LateDecode
-- END copied JFs_LateDecode
-- BEGIN copied JFt_Digest43: lean/JFt_Digest43.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest43
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [71235157#u32,561336479#u32,2021715933#u32,831357912#u32,593948515#u32,110335229#u32,1732475008#u32,949858646#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest43.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest43.window
    NFY_JFu_PublicDigest43.length NFY_JFu_PublicDigest43.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest43.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest43.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1744 32 (by decide)=NFY_JFu_PublicDigest43.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest43.window]
  exact NFY_JFu_PublicDigest43.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1744 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest43
-- END copied JFt_Digest43
-- BEGIN copied JFt_Digest44: lean/JFt_Digest44.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest44
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [8526811#u32,109678668#u32,1639079956#u32,402852#u32,1893371776#u32,347120802#u32,331397657#u32,1970188241#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest44.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest44.window
    NFY_JFu_PublicDigest44.length NFY_JFu_PublicDigest44.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest44.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest44.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1776 32 (by decide)=NFY_JFu_PublicDigest44.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest44.window]
  exact NFY_JFu_PublicDigest44.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1776 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest44
-- END copied JFt_Digest44
-- BEGIN copied JFt_Digest45: lean/JFt_Digest45.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest45
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [1443258150#u32,390107157#u32,739124880#u32,1925983251#u32,420127778#u32,800761649#u32,949547039#u32,74873928#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest45.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest45.window
    NFY_JFu_PublicDigest45.length NFY_JFu_PublicDigest45.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest45.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest45.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1816 32 (by decide)=NFY_JFu_PublicDigest45.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest45.window]
  exact NFY_JFu_PublicDigest45.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1816 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest45
-- END copied JFt_Digest45
-- BEGIN copied JFt_Digest46: lean/JFt_Digest46.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Digest46
open Aeneas Aeneas.Std Result

def value : Array AspisR1TerminalDecoder.aspis_core.field.M31 8#usize :=
  Array.make 8#usize [109581603#u32,2018382657#u32,1175266929#u32,551563770#u32,389056008#u32,563172097#u32,1431420963#u32,351017421#u32]

/-- Exact numeric value is identified by the symbolic byte-injectivity lemma. -/
theorem local_call : AspisS6NativeSnapshotReadDigest.read_digest NFY_JFu_PublicDigest46.window=ok (.Ok value) := by
  obtain ⟨out,call,canon,contents⟩:=NFY_JFu_DigestSliceFacts.source NFY_JFu_PublicDigest46.window
    NFY_JFu_PublicDigest46.length NFY_JFu_PublicDigest46.canonical_bytes
  have bytes : AspisS6SourceCodec.DigestContents.chunks value=NFY_JFu_PublicDigest46.bytes := by
    simp [AspisS6SourceCodec.DigestContents.chunks,value,Array.make,core.num.U32.to_le_bytes,BitVec.toLEBytes,NFY_JFu_PublicDigest46.bytes]
    <;> (repeat' constructor) <;> scalar_tac
  have same : out=value := NFY_JFt_DigestInjective.injective out value (contents.trans bytes.symm)
  rw [same] at call
  exact call

theorem selected : NFY_JFu_PublicRange.segment 1848 32 (by decide)=NFY_JFu_PublicDigest46.window := by
  apply Subtype.ext
  dsimp only [NFY_JFu_PublicRange.segment,NFY_JFu_PublicDigest46.window]
  exact NFY_JFu_PublicDigest46.selected

theorem source : AspisS6NativeSnapshotReadDigest.read_digest
    (NFY_JFu_PublicRange.segment 1848 32 (by decide))=ok (.Ok value) := by
  rw [selected]
  exact local_call

theorem canonical : NFY_JFu_DigestCanonical.Canonical value :=
  NFY_JFu_DigestSliceCanonical.source _ _ source

#print axioms local_call
#print axioms selected
#print axioms source
#print axioms canonical
end AspisR1.NFY_JFt_Digest46
-- END copied JFt_Digest46

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
