import JHg_AuditLane
import JHg_World
import JFt_SnapshotValue
import JFu_PublicDigest01
import JFu_PublicDigest02
import JFu_PublicDigest03
import JFu_PublicDigest04
import JFu_PublicDigest05
import JFu_PublicDigest06
import JFu_PublicDigest07
import JFu_PublicDigest08
import JFu_PublicDigest09
import JFu_PublicDigest10
import JFu_PublicDigest11
import JFu_PublicDigest12
import JFu_PublicDigest13
import JFu_PublicDigest14
import JFu_PublicDigest15
import JFu_PublicDigest16
import JFu_PublicDigest17
import JFu_PublicDigest18
import JFu_PublicDigest19
import JFu_PublicDigest20
import JFu_PublicDigest21
set_option autoImplicit false
namespace AspisR1.JHg_BindingsLane
open Aeneas Aeneas.Std Result
theorem master : (JHb_DataLane.bytes.drop 40).take 32=(JHg_World.e2.snapshot 1 384 384).key.val := by
  rw [JHg_AuditLane.master];rfl
#print axioms master
theorem root : (JHb_DataLane.bytes.drop 96).take 32=(JFx_NativeBytes.publicInput.val.drop 304).take 32 := by
  rw [JHg_AuditLane.root,JFu_PublicDigest01.selected];rfl
#print axioms root
theorem frontier_0 : (JHb_DataLane.bytes.drop 128).take 32=(JFx_NativeBytes.publicInput.val.drop 336).take 32 := by
  rw [JHg_AuditLane.frontier_0,JFu_PublicDigest02.selected];rfl
#print axioms frontier_0
theorem frontier_1 : (JHb_DataLane.bytes.drop 160).take 32=(JFx_NativeBytes.publicInput.val.drop 368).take 32 := by
  rw [JHg_AuditLane.frontier_1,JFu_PublicDigest03.selected];rfl
#print axioms frontier_1
theorem frontier_2 : (JHb_DataLane.bytes.drop 192).take 32=(JFx_NativeBytes.publicInput.val.drop 400).take 32 := by
  rw [JHg_AuditLane.frontier_2,JFu_PublicDigest04.selected];rfl
#print axioms frontier_2
theorem frontier_3 : (JHb_DataLane.bytes.drop 224).take 32=(JFx_NativeBytes.publicInput.val.drop 432).take 32 := by
  rw [JHg_AuditLane.frontier_3,JFu_PublicDigest05.selected];rfl
#print axioms frontier_3
theorem frontier_4 : (JHb_DataLane.bytes.drop 256).take 32=(JFx_NativeBytes.publicInput.val.drop 464).take 32 := by
  rw [JHg_AuditLane.frontier_4,JFu_PublicDigest06.selected];rfl
#print axioms frontier_4
theorem frontier_5 : (JHb_DataLane.bytes.drop 288).take 32=(JFx_NativeBytes.publicInput.val.drop 496).take 32 := by
  rw [JHg_AuditLane.frontier_5,JFu_PublicDigest07.selected];rfl
#print axioms frontier_5
theorem frontier_6 : (JHb_DataLane.bytes.drop 320).take 32=(JFx_NativeBytes.publicInput.val.drop 528).take 32 := by
  rw [JHg_AuditLane.frontier_6,JFu_PublicDigest08.selected];rfl
#print axioms frontier_6
theorem frontier_7 : (JHb_DataLane.bytes.drop 352).take 32=(JFx_NativeBytes.publicInput.val.drop 560).take 32 := by
  rw [JHg_AuditLane.frontier_7,JFu_PublicDigest09.selected];rfl
#print axioms frontier_7
theorem frontier_8 : (JHb_DataLane.bytes.drop 384).take 32=(JFx_NativeBytes.publicInput.val.drop 592).take 32 := by
  rw [JHg_AuditLane.frontier_8,JFu_PublicDigest10.selected];rfl
#print axioms frontier_8
theorem frontier_9 : (JHb_DataLane.bytes.drop 416).take 32=(JFx_NativeBytes.publicInput.val.drop 624).take 32 := by
  rw [JHg_AuditLane.frontier_9,JFu_PublicDigest11.selected];rfl
#print axioms frontier_9
theorem frontier_10 : (JHb_DataLane.bytes.drop 448).take 32=(JFx_NativeBytes.publicInput.val.drop 656).take 32 := by
  rw [JHg_AuditLane.frontier_10,JFu_PublicDigest12.selected];rfl
#print axioms frontier_10
theorem frontier_11 : (JHb_DataLane.bytes.drop 480).take 32=(JFx_NativeBytes.publicInput.val.drop 688).take 32 := by
  rw [JHg_AuditLane.frontier_11,JFu_PublicDigest13.selected];rfl
#print axioms frontier_11
theorem frontier_12 : (JHb_DataLane.bytes.drop 512).take 32=(JFx_NativeBytes.publicInput.val.drop 720).take 32 := by
  rw [JHg_AuditLane.frontier_12,JFu_PublicDigest14.selected];rfl
#print axioms frontier_12
theorem frontier_13 : (JHb_DataLane.bytes.drop 544).take 32=(JFx_NativeBytes.publicInput.val.drop 752).take 32 := by
  rw [JHg_AuditLane.frontier_13,JFu_PublicDigest15.selected];rfl
#print axioms frontier_13
theorem frontier_14 : (JHb_DataLane.bytes.drop 576).take 32=(JFx_NativeBytes.publicInput.val.drop 784).take 32 := by
  rw [JHg_AuditLane.frontier_14,JFu_PublicDigest16.selected];rfl
#print axioms frontier_14
theorem frontier_15 : (JHb_DataLane.bytes.drop 608).take 32=(JFx_NativeBytes.publicInput.val.drop 816).take 32 := by
  rw [JHg_AuditLane.frontier_15,JFu_PublicDigest17.selected];rfl
#print axioms frontier_15
theorem frontier_16 : (JHb_DataLane.bytes.drop 640).take 32=(JFx_NativeBytes.publicInput.val.drop 848).take 32 := by
  rw [JHg_AuditLane.frontier_16,JFu_PublicDigest18.selected];rfl
#print axioms frontier_16
theorem frontier_17 : (JHb_DataLane.bytes.drop 672).take 32=(JFx_NativeBytes.publicInput.val.drop 880).take 32 := by
  rw [JHg_AuditLane.frontier_17,JFu_PublicDigest19.selected];rfl
#print axioms frontier_17
theorem frontier_18 : (JHb_DataLane.bytes.drop 704).take 32=(JFx_NativeBytes.publicInput.val.drop 912).take 32 := by
  rw [JHg_AuditLane.frontier_18,JFu_PublicDigest20.selected];rfl
#print axioms frontier_18
theorem frontier_19 : (JHb_DataLane.bytes.drop 736).take 32=(JFx_NativeBytes.publicInput.val.drop 944).take 32 := by
  rw [JHg_AuditLane.frontier_19,JFu_PublicDigest21.selected];rfl
#print axioms frontier_19
end AspisR1.JHg_BindingsLane
