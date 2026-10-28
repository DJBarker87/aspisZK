import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot01_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[33#u8,207#u8,152#u8,112#u8,156#u8,202#u8,65#u8,119#u8,121#u8,96#u8,128#u8,4#u8,42#u8,202#u8,18#u8,104#u8,168#u8,25#u8,193#u8,46#u8,234#u8,198#u8,215#u8,72#u8,206#u8,145#u8,40#u8,84#u8,178#u8,37#u8,26#u8,77#u8,174#u8,81#u8,5#u8,117#u8,194#u8,38#u8,164#u8,50#u8,165#u8,99#u8,226#u8,63#u8,113#u8,63#u8,13#u8,5#u8,127#u8,29#u8,102#u8,117#u8,176#u8,58#u8,155#u8,67#u8,225#u8,181#u8,112#u8,101#u8,197#u8,45#u8,146#u8,50#u8,30#u8,12#u8,88#u8,55#u8,63#u8,108#u8,109#u8,32#u8,14#u8,225#u8,79#u8,86#u8,148#u8,244#u8,217#u8,84#u8,48#u8,112#u8,19#u8,49#u8,68#u8,78#u8,216#u8,127#u8,106#u8,117#u8,152#u8,89#u8,90#u8,79#u8,196#u8,44#u8,76#u8,162#u8,122#u8,31#u8,18#u8,86#u8,182#u8,120#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1889062689#u32,2000800412#u32,75522169#u32,1746061866#u32,784406952#u32,1222100714#u32,1411944910#u32,1293559218#u32,1963282862#u32,849618626#u32,1071801253#u32,84754289#u32,1969626495#u32,1134246576#u32,1701885409#u32,848440773#u32,928517150#u32,544042047#u32,1448075534#u32,1423570068#u32,823357488#u32,2144882244#u32,1503163754#u32,751062874#u32,528130636#u32,2025215506#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1889062689#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1889062689<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 2000800412#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2000800412<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 75522169#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 75522169<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1746061866#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1746061866<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 784406952#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 784406952<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1222100714#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1222100714<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1411944910#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1411944910<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1293559218#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1293559218<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1963282862#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1963282862<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 849618626#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 849618626<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1071801253#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1071801253<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 84754289#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 84754289<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1969626495#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1969626495<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1134246576#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1134246576<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1701885409#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1701885409<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 848440773#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 848440773<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 928517150#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 928517150<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 544042047#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 544042047<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1448075534#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1448075534<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1423570068#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1423570068<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 823357488#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 823357488<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 2144882244#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2144882244<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1503163754#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1503163754<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 751062874#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 751062874<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 528130636#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 528130636<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 2025215506#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2025215506<2147483647;omega)
#print axioms decode25

theorem decode (t : Fin 26) : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw t)=
    ok (some (values.val[t.val]'(by rw [values.property];exact t.isLt))) := by
  fin_cases t
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13
  · exact decode14
  · exact decode15
  · exact decode16
  · exact decode17
  · exact decode18
  · exact decode19
  · exact decode20
  · exact decode21
  · exact decode22
  · exact decode23
  · exact decode24
  · exact decode25

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨1,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨1,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot01_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot01_1
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[250#u8,207#u8,171#u8,92#u8,220#u8,204#u8,233#u8,72#u8,249#u8,61#u8,13#u8,108#u8,102#u8,1#u8,114#u8,37#u8,47#u8,117#u8,64#u8,94#u8,193#u8,71#u8,211#u8,8#u8,15#u8,36#u8,66#u8,97#u8,245#u8,100#u8,197#u8,30#u8,67#u8,190#u8,152#u8,8#u8,40#u8,37#u8,158#u8,59#u8,121#u8,99#u8,98#u8,109#u8,83#u8,228#u8,194#u8,1#u8,106#u8,118#u8,89#u8,74#u8,20#u8,87#u8,84#u8,74#u8,156#u8,75#u8,75#u8,107#u8,140#u8,30#u8,69#u8,122#u8,80#u8,226#u8,199#u8,68#u8,31#u8,4#u8,189#u8,67#u8,254#u8,26#u8,73#u8,25#u8,113#u8,22#u8,34#u8,80#u8,139#u8,194#u8,198#u8,61#u8,62#u8,72#u8,206#u8,93#u8,142#u8,223#u8,208#u8,115#u8,145#u8,73#u8,208#u8,5#u8,173#u8,153#u8,53#u8,41#u8,205#u8,29#u8,83#u8,4#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1554763770#u32,1223281884#u32,1812807161#u32,628228454#u32,1581282607#u32,148064193#u32,1631724559#u32,516252917#u32,144227907#u32,1000219944#u32,1835164537#u32,29549651#u32,1247377002#u32,1247041300#u32,1800096668#u32,2051350156#u32,1153950288#u32,1136460831#u32,424221438#u32,1344411249#u32,1036436107#u32,1573799998#u32,1943068558#u32,97536401#u32,691378605#u32,72555981#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop 120).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 120 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1554763770#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1554763770<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1223281884#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1223281884<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1812807161#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1812807161<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 628228454#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 628228454<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1581282607#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1581282607<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 148064193#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 148064193<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1631724559#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1631724559<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 516252917#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 516252917<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 144227907#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 144227907<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1000219944#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1000219944<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1835164537#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1835164537<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 29549651#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 29549651<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1247377002#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1247377002<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1247041300#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1247041300<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1800096668#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1800096668<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 2051350156#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2051350156<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1153950288#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1153950288<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1136460831#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1136460831<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 424221438#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 424221438<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1344411249#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1344411249<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1036436107#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1036436107<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1573799998#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1573799998<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1943068558#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1943068558<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 97536401#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 97536401<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 691378605#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 691378605<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 72555981#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 72555981<2147483647;omega)
#print axioms decode25

theorem decode (t : Fin 26) : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw t)=
    ok (some (values.val[t.val]'(by rw [values.property];exact t.isLt))) := by
  fin_cases t
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13
  · exact decode14
  · exact decode15
  · exact decode16
  · exact decode17
  · exact decode18
  · exact decode19
  · exact decode20
  · exact decode21
  · exact decode22
  · exact decode23
  · exact decode24
  · exact decode25

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨1,by decide⟩)
    1#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop (120*1+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨1,by decide⟩).val 120 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot01_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot01_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[97#u8,23#u8,128#u8,82#u8,106#u8,176#u8,4#u8,112#u8,128#u8,121#u8,134#u8,80#u8,156#u8,195#u8,108#u8,124#u8,183#u8,37#u8,72#u8,47#u8,53#u8,254#u8,186#u8,48#u8,31#u8,186#u8,5#u8,47#u8,78#u8,154#u8,78#u8,25#u8,57#u8,1#u8,143#u8,13#u8,20#u8,217#u8,179#u8,36#u8,218#u8,225#u8,3#u8,86#u8,38#u8,225#u8,151#u8,17#u8,242#u8,165#u8,111#u8,49#u8,196#u8,75#u8,238#u8,60#u8,213#u8,205#u8,166#u8,127#u8,206#u8,31#u8,173#u8,93#u8,216#u8,236#u8,249#u8,21#u8,243#u8,200#u8,77#u8,79#u8,69#u8,18#u8,24#u8,41#u8,156#u8,119#u8,247#u8,91#u8,106#u8,66#u8,80#u8,67#u8,180#u8,226#u8,230#u8,13#u8,81#u8,39#u8,29#u8,77#u8,27#u8,153#u8,254#u8,124#u8,254#u8,80#u8,20#u8,36#u8,120#u8,155#u8,121#u8,33#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1384126305#u32,1879355498#u32,1350990208#u32,2087502748#u32,793257399#u32,817561141#u32,788904479#u32,424581710#u32,227475769#u32,615766292#u32,1443095002#u32,295166246#u32,829400562#u32,1022249924#u32,2141638101#u32,1571626958#u32,368700632#u32,1330497779#u32,689443397#u32,1542944668#u32,1129333354#u32,233235124#u32,1293756241#u32,2097060123#u32,605311230#u32,561617784#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1384126305#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1384126305<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1879355498#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1879355498<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1350990208#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1350990208<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 2087502748#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2087502748<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 793257399#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 793257399<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 817561141#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 817561141<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 788904479#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 788904479<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 424581710#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 424581710<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 227475769#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 227475769<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 615766292#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 615766292<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1443095002#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1443095002<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 295166246#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 295166246<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 829400562#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 829400562<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1022249924#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1022249924<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 2141638101#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2141638101<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1571626958#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1571626958<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 368700632#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 368700632<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1330497779#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1330497779<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 689443397#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 689443397<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1542944668#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1542944668<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1129333354#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1129333354<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 233235124#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 233235124<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1293756241#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1293756241<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 2097060123#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2097060123<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 605311230#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 605311230<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 561617784#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 561617784<2147483647;omega)
#print axioms decode25

theorem decode (t : Fin 26) : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw t)=
    ok (some (values.val[t.val]'(by rw [values.property];exact t.isLt))) := by
  fin_cases t
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13
  · exact decode14
  · exact decode15
  · exact decode16
  · exact decode17
  · exact decode18
  · exact decode19
  · exact decode20
  · exact decode21
  · exact decode22
  · exact decode23
  · exact decode24
  · exact decode25

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨1,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨1,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot01_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot01_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[233#u8,150#u8,247#u8,83#u8,158#u8,105#u8,6#u8,55#u8,207#u8,12#u8,91#u8,113#u8,164#u8,80#u8,60#u8,30#u8,218#u8,209#u8,30#u8,81#u8,127#u8,232#u8,207#u8,66#u8,244#u8,195#u8,163#u8,56#u8,2#u8,118#u8,187#u8,31#u8,194#u8,244#u8,184#u8,92#u8,245#u8,254#u8,94#u8,58#u8,14#u8,78#u8,46#u8,98#u8,62#u8,250#u8,33#u8,36#u8,95#u8,165#u8,208#u8,60#u8,158#u8,206#u8,190#u8,16#u8,153#u8,52#u8,145#u8,35#u8,101#u8,182#u8,93#u8,84#u8,245#u8,251#u8,58#u8,126#u8,41#u8,34#u8,90#u8,114#u8,50#u8,144#u8,226#u8,26#u8,179#u8,100#u8,171#u8,93#u8,93#u8,139#u8,28#u8,112#u8,103#u8,32#u8,63#u8,102#u8,100#u8,92#u8,99#u8,72#u8,103#u8,167#u8,241#u8,101#u8,11#u8,164#u8,88#u8,75#u8,133#u8,97#u8,118#u8,10#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1408734953#u32,923167134#u32,1901792463#u32,507269284#u32,1360974298#u32,1120921727#u32,950256628#u32,532379138#u32,1555625154#u32,979304181#u32,1647201806#u32,606206526#u32,1020306783#u32,280940190#u32,596718745#u32,1415427685#u32,2117794805#u32,1918509609#u32,451055666#u32,1571513523#u32,1880918877#u32,1715413095#u32,1214471268#u32,1710335847#u32,1264100363#u32,175530373#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1408734953#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1408734953<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 923167134#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 923167134<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1901792463#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1901792463<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 507269284#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 507269284<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1360974298#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1360974298<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1120921727#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1120921727<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 950256628#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 950256628<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 532379138#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 532379138<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1555625154#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1555625154<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 979304181#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 979304181<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1647201806#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1647201806<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 606206526#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 606206526<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1020306783#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1020306783<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 280940190#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 280940190<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 596718745#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 596718745<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1415427685#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1415427685<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 2117794805#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2117794805<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1918509609#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1918509609<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 451055666#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 451055666<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1571513523#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1571513523<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1880918877#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1880918877<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1715413095#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1715413095<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1214471268#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1214471268<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1710335847#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1710335847<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1264100363#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1264100363<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 175530373#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 175530373<2147483647;omega)
#print axioms decode25

theorem decode (t : Fin 26) : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw t)=
    ok (some (values.val[t.val]'(by rw [values.property];exact t.isLt))) := by
  fin_cases t
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13
  · exact decode14
  · exact decode15
  · exact decode16
  · exact decode17
  · exact decode18
  · exact decode19
  · exact decode20
  · exact decode21
  · exact decode22
  · exact decode23
  · exact decode24
  · exact decode25

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨1,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨1,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨1,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot01_3
end
