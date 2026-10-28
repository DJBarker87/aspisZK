import NDO_JGz_SHAC00
import NDO_JGz_SHAC01
import RPz8_JFx_DataCheckpoint00
set_option autoImplicit false
namespace AspisR1.JGz_ChecksumNative
open Aeneas Aeneas.Std
def domain : List U8 := [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,58#u8,82#u8,49#u8,58#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8]
def chunks : List (List Nat) := [JGz_SHAC00.B000.input,JGz_SHAC00.B001.input,JGz_SHAC00.B002.input,JGz_SHAC00.B003.input,JGz_SHAC00.B004.input,JGz_SHAC00.B005.input,JGz_SHAC00.B006.input,JGz_SHAC00.B007.input,JGz_SHAC00.B008.input,JGz_SHAC00.B009.input,JGz_SHAC00.B010.input,JGz_SHAC00.B011.input,JGz_SHAC00.B012.input,JGz_SHAC00.B013.input,JGz_SHAC00.B014.input,JGz_SHAC00.B015.input,JGz_SHAC01.B016.input,JGz_SHAC01.B017.input,JGz_SHAC01.B018.input,JGz_SHAC01.B019.input,JGz_SHAC01.B020.input,JGz_SHAC01.B021.input,JGz_SHAC01.B022.input,JGz_SHAC01.B023.input,JGz_SHAC01.B024.input,JGz_SHAC01.B025.input,JGz_SHAC01.B026.input]
def tail : List Nat := [213,90,177,248,165,18,231,136,56,116,131,101,183,94,130,208,101,85,96,211,67,53,23,7,176,65,47,32,136,15]
def raw : List Nat := chunks.flatten ++ tail
theorem cell00 : JGz_SHAC00.B000.input=(domain ++ JFx_DataCheckpoint00.c00 ++ JFx_DataCheckpoint00.c01.take 10).map (fun x=>x.val) := by rfl
#print axioms cell00
theorem cell01 : JGz_SHAC00.B001.input=(JFx_DataCheckpoint00.c01.drop 10 ++ JFx_DataCheckpoint00.c02 ++ JFx_DataCheckpoint00.c03.take 10).map (fun x=>x.val) := by rfl
#print axioms cell01
theorem cell02 : JGz_SHAC00.B002.input=(JFx_DataCheckpoint00.c03.drop 10 ++ JFx_DataCheckpoint00.c04 ++ JFx_DataCheckpoint00.c05.take 10).map (fun x=>x.val) := by rfl
#print axioms cell02
theorem cell03 : JGz_SHAC00.B003.input=(JFx_DataCheckpoint00.c05.drop 10 ++ JFx_DataCheckpoint00.c06 ++ JFx_DataCheckpoint00.c07.take 10).map (fun x=>x.val) := by rfl
#print axioms cell03
theorem cell04 : JGz_SHAC00.B004.input=(JFx_DataCheckpoint00.c07.drop 10 ++ JFx_DataCheckpoint00.c08 ++ JFx_DataCheckpoint00.c09.take 10).map (fun x=>x.val) := by rfl
#print axioms cell04
theorem cell05 : JGz_SHAC00.B005.input=(JFx_DataCheckpoint00.c09.drop 10 ++ JFx_DataCheckpoint00.c10 ++ JFx_DataCheckpoint00.c11.take 10).map (fun x=>x.val) := by rfl
#print axioms cell05
theorem cell06 : JGz_SHAC00.B006.input=(JFx_DataCheckpoint00.c11.drop 10 ++ JFx_DataCheckpoint00.c12 ++ JFx_DataCheckpoint00.c13.take 10).map (fun x=>x.val) := by rfl
#print axioms cell06
theorem cell07 : JGz_SHAC00.B007.input=(JFx_DataCheckpoint00.c13.drop 10 ++ JFx_DataCheckpoint00.c14 ++ JFx_DataCheckpoint00.c15.take 10).map (fun x=>x.val) := by rfl
#print axioms cell07
theorem cell08 : JGz_SHAC00.B008.input=(JFx_DataCheckpoint00.c15.drop 10 ++ JFx_DataCheckpoint00.c16 ++ JFx_DataCheckpoint00.c17.take 10).map (fun x=>x.val) := by rfl
#print axioms cell08
theorem cell09 : JGz_SHAC00.B009.input=(JFx_DataCheckpoint00.c17.drop 10 ++ JFx_DataCheckpoint00.c18 ++ JFx_DataCheckpoint00.c19.take 10).map (fun x=>x.val) := by rfl
#print axioms cell09
theorem cell10 : JGz_SHAC00.B010.input=(JFx_DataCheckpoint00.c19.drop 10 ++ JFx_DataCheckpoint00.c20 ++ JFx_DataCheckpoint00.c21.take 10).map (fun x=>x.val) := by rfl
#print axioms cell10
theorem cell11 : JGz_SHAC00.B011.input=(JFx_DataCheckpoint00.c21.drop 10 ++ JFx_DataCheckpoint00.c22 ++ JFx_DataCheckpoint00.c23.take 10).map (fun x=>x.val) := by rfl
#print axioms cell11
theorem cell12 : JGz_SHAC00.B012.input=(JFx_DataCheckpoint00.c23.drop 10 ++ JFx_DataCheckpoint00.c24 ++ JFx_DataCheckpoint00.c25.take 10).map (fun x=>x.val) := by rfl
#print axioms cell12
theorem cell13 : JGz_SHAC00.B013.input=(JFx_DataCheckpoint00.c25.drop 10 ++ JFx_DataCheckpoint00.c26 ++ JFx_DataCheckpoint00.c27.take 10).map (fun x=>x.val) := by rfl
#print axioms cell13
theorem cell14 : JGz_SHAC00.B014.input=(JFx_DataCheckpoint00.c27.drop 10 ++ JFx_DataCheckpoint00.c28 ++ JFx_DataCheckpoint00.c29.take 10).map (fun x=>x.val) := by rfl
#print axioms cell14
theorem cell15 : JGz_SHAC00.B015.input=(JFx_DataCheckpoint00.c29.drop 10 ++ JFx_DataCheckpoint00.c30 ++ JFx_DataCheckpoint00.c31.take 10).map (fun x=>x.val) := by rfl
#print axioms cell15
theorem cell16 : JGz_SHAC01.B016.input=(JFx_DataCheckpoint00.c31.drop 10 ++ JFx_DataCheckpoint00.c32 ++ JFx_DataCheckpoint00.c33.take 10).map (fun x=>x.val) := by rfl
#print axioms cell16
theorem cell17 : JGz_SHAC01.B017.input=(JFx_DataCheckpoint00.c33.drop 10 ++ JFx_DataCheckpoint00.c34 ++ JFx_DataCheckpoint00.c35.take 10).map (fun x=>x.val) := by rfl
#print axioms cell17
theorem cell18 : JGz_SHAC01.B018.input=(JFx_DataCheckpoint00.c35.drop 10 ++ JFx_DataCheckpoint00.c36 ++ JFx_DataCheckpoint00.c37.take 10).map (fun x=>x.val) := by rfl
#print axioms cell18
theorem cell19 : JGz_SHAC01.B019.input=(JFx_DataCheckpoint00.c37.drop 10 ++ JFx_DataCheckpoint00.c38 ++ JFx_DataCheckpoint00.c39.take 10).map (fun x=>x.val) := by rfl
#print axioms cell19
theorem cell20 : JGz_SHAC01.B020.input=(JFx_DataCheckpoint00.c39.drop 10 ++ JFx_DataCheckpoint00.c40 ++ JFx_DataCheckpoint00.c41.take 10).map (fun x=>x.val) := by rfl
#print axioms cell20
theorem cell21 : JGz_SHAC01.B021.input=(JFx_DataCheckpoint00.c41.drop 10 ++ JFx_DataCheckpoint00.c42 ++ JFx_DataCheckpoint00.c43.take 10).map (fun x=>x.val) := by rfl
#print axioms cell21
theorem cell22 : JGz_SHAC01.B022.input=(JFx_DataCheckpoint00.c43.drop 10 ++ JFx_DataCheckpoint00.c44 ++ JFx_DataCheckpoint00.c45.take 10).map (fun x=>x.val) := by rfl
#print axioms cell22
theorem cell23 : JGz_SHAC01.B023.input=(JFx_DataCheckpoint00.c45.drop 10 ++ JFx_DataCheckpoint00.c46 ++ JFx_DataCheckpoint00.c47.take 10).map (fun x=>x.val) := by rfl
#print axioms cell23
theorem cell24 : JGz_SHAC01.B024.input=(JFx_DataCheckpoint00.c47.drop 10 ++ JFx_DataCheckpoint00.c48 ++ JFx_DataCheckpoint00.c49.take 10).map (fun x=>x.val) := by rfl
#print axioms cell24
theorem cell25 : JGz_SHAC01.B025.input=(JFx_DataCheckpoint00.c49.drop 10 ++ JFx_DataCheckpoint00.c50 ++ JFx_DataCheckpoint00.c51.take 10).map (fun x=>x.val) := by rfl
#print axioms cell25
theorem cell26 : JGz_SHAC01.B026.input=(JFx_DataCheckpoint00.c51.drop 10 ++ JFx_DataCheckpoint00.c52 ++ JFx_DataCheckpoint00.c53.take 10).map (fun x=>x.val) := by rfl
#print axioms cell26
theorem tail_native : tail=(JFx_DataCheckpoint00.c53.drop 10 ++ JFx_DataCheckpoint00.c54.take 8).map (fun x=>x.val) := by rfl
#print axioms tail_native
def retainedHead : List U8 := JFx_DataCheckpoint00.c00 ++ JFx_DataCheckpoint00.c01 ++ JFx_DataCheckpoint00.c02 ++ JFx_DataCheckpoint00.c03 ++ JFx_DataCheckpoint00.c04 ++ JFx_DataCheckpoint00.c05 ++ JFx_DataCheckpoint00.c06 ++ JFx_DataCheckpoint00.c07 ++ JFx_DataCheckpoint00.c08 ++ JFx_DataCheckpoint00.c09 ++ JFx_DataCheckpoint00.c10 ++ JFx_DataCheckpoint00.c11 ++ JFx_DataCheckpoint00.c12 ++ JFx_DataCheckpoint00.c13 ++ JFx_DataCheckpoint00.c14 ++ JFx_DataCheckpoint00.c15 ++ JFx_DataCheckpoint00.c16 ++ JFx_DataCheckpoint00.c17 ++ JFx_DataCheckpoint00.c18 ++ JFx_DataCheckpoint00.c19 ++ JFx_DataCheckpoint00.c20 ++ JFx_DataCheckpoint00.c21 ++ JFx_DataCheckpoint00.c22 ++ JFx_DataCheckpoint00.c23 ++ JFx_DataCheckpoint00.c24 ++ JFx_DataCheckpoint00.c25 ++ JFx_DataCheckpoint00.c26 ++ JFx_DataCheckpoint00.c27 ++ JFx_DataCheckpoint00.c28 ++ JFx_DataCheckpoint00.c29 ++ JFx_DataCheckpoint00.c30 ++ JFx_DataCheckpoint00.c31 ++ JFx_DataCheckpoint00.c32 ++ JFx_DataCheckpoint00.c33 ++ JFx_DataCheckpoint00.c34 ++ JFx_DataCheckpoint00.c35 ++ JFx_DataCheckpoint00.c36 ++ JFx_DataCheckpoint00.c37 ++ JFx_DataCheckpoint00.c38 ++ JFx_DataCheckpoint00.c39 ++ JFx_DataCheckpoint00.c40 ++ JFx_DataCheckpoint00.c41 ++ JFx_DataCheckpoint00.c42 ++ JFx_DataCheckpoint00.c43 ++ JFx_DataCheckpoint00.c44 ++ JFx_DataCheckpoint00.c45 ++ JFx_DataCheckpoint00.c46 ++ JFx_DataCheckpoint00.c47 ++ JFx_DataCheckpoint00.c48 ++ JFx_DataCheckpoint00.c49 ++ JFx_DataCheckpoint00.c50 ++ JFx_DataCheckpoint00.c51 ++ JFx_DataCheckpoint00.c52 ++ JFx_DataCheckpoint00.c53 ++ JFx_DataCheckpoint00.c54.take 8
theorem cut : JFx_DataCheckpoint00.bytes.take 1736=retainedHead := by
  simp only [JFx_DataCheckpoint00.bytes,retainedHead,List.take_append,List.length_append,JFx_DataCheckpoint00.c00_length,JFx_DataCheckpoint00.c01_length,JFx_DataCheckpoint00.c02_length,JFx_DataCheckpoint00.c03_length,JFx_DataCheckpoint00.c04_length,JFx_DataCheckpoint00.c05_length,JFx_DataCheckpoint00.c06_length,JFx_DataCheckpoint00.c07_length,JFx_DataCheckpoint00.c08_length,JFx_DataCheckpoint00.c09_length,JFx_DataCheckpoint00.c10_length,JFx_DataCheckpoint00.c11_length,JFx_DataCheckpoint00.c12_length,JFx_DataCheckpoint00.c13_length,JFx_DataCheckpoint00.c14_length,JFx_DataCheckpoint00.c15_length,JFx_DataCheckpoint00.c16_length,JFx_DataCheckpoint00.c17_length,JFx_DataCheckpoint00.c18_length,JFx_DataCheckpoint00.c19_length,JFx_DataCheckpoint00.c20_length,JFx_DataCheckpoint00.c21_length,JFx_DataCheckpoint00.c22_length,JFx_DataCheckpoint00.c23_length,JFx_DataCheckpoint00.c24_length,JFx_DataCheckpoint00.c25_length,JFx_DataCheckpoint00.c26_length,JFx_DataCheckpoint00.c27_length,JFx_DataCheckpoint00.c28_length,JFx_DataCheckpoint00.c29_length,JFx_DataCheckpoint00.c30_length,JFx_DataCheckpoint00.c31_length,JFx_DataCheckpoint00.c32_length,JFx_DataCheckpoint00.c33_length,JFx_DataCheckpoint00.c34_length,JFx_DataCheckpoint00.c35_length,JFx_DataCheckpoint00.c36_length,JFx_DataCheckpoint00.c37_length,JFx_DataCheckpoint00.c38_length,JFx_DataCheckpoint00.c39_length,JFx_DataCheckpoint00.c40_length,JFx_DataCheckpoint00.c41_length,JFx_DataCheckpoint00.c42_length,JFx_DataCheckpoint00.c43_length,JFx_DataCheckpoint00.c44_length,JFx_DataCheckpoint00.c45_length,JFx_DataCheckpoint00.c46_length,JFx_DataCheckpoint00.c47_length,JFx_DataCheckpoint00.c48_length,JFx_DataCheckpoint00.c49_length,JFx_DataCheckpoint00.c50_length,JFx_DataCheckpoint00.c51_length,JFx_DataCheckpoint00.c52_length,JFx_DataCheckpoint00.c53_length,JFx_DataCheckpoint00.c54_length,JFx_DataCheckpoint00.c55_length,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.take_of_length_le,List.take_zero,List.append_nil,List.append_assoc]
#print axioms cut
theorem split_join {A : Type} (xs rest : List A) (n : Nat) : xs.take n ++ (xs.drop n ++ rest)=xs ++ rest := by
  rw [←List.append_assoc,List.take_append_drop]
#print axioms split_join
theorem native : (domain ++ JFx_DataCheckpoint00.bytes.take 1736).map (fun x=>x.val)=raw := by
  rw [cut]
  unfold raw chunks
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
  rw [cell00,cell01,cell02,cell03,cell04,cell05,cell06,cell07,cell08,cell09,cell10,cell11,cell12,cell13,cell14,cell15,cell16,cell17,cell18,cell19,cell20,cell21,cell22,cell23,cell24,cell25,cell26,tail_native]
  simp only [retainedHead,List.map_append,List.map_take,List.map_drop,List.append_assoc,split_join]
#print axioms native
end AspisR1.JGz_ChecksumNative
