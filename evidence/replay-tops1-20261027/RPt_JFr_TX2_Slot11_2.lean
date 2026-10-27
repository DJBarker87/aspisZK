import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Slot11_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[15#u8,161#u8,183#u8,118#u8,254#u8,243#u8,210#u8,123#u8,201#u8,28#u8,173#u8,8#u8,44#u8,223#u8,139#u8,56#u8,86#u8,233#u8,117#u8,125#u8,248#u8,17#u8,72#u8,77#u8,204#u8,123#u8,238#u8,47#u8,228#u8,220#u8,137#u8,40#u8,127#u8,160#u8,14#u8,7#u8,228#u8,158#u8,194#u8,63#u8,237#u8,99#u8,108#u8,116#u8,38#u8,18#u8,250#u8,120#u8,232#u8,165#u8,149#u8,40#u8,19#u8,232#u8,238#u8,121#u8,175#u8,241#u8,75#u8,3#u8,69#u8,242#u8,160#u8,23#u8,105#u8,153#u8,152#u8,69#u8,184#u8,73#u8,124#u8,21#u8,168#u8,115#u8,145#u8,104#u8,29#u8,58#u8,86#u8,99#u8,236#u8,188#u8,3#u8,11#u8,195#u8,203#u8,67#u8,20#u8,236#u8,107#u8,111#u8,113#u8,71#u8,97#u8,255#u8,121#u8,191#u8,35#u8,178#u8,106#u8,139#u8,159#u8,215#u8,91#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1991745807#u32,2077422590#u32,145562825#u32,948690732#u32,2104879446#u32,1296568824#u32,804158412#u32,680123620#u32,118399103#u32,1069719268#u32,1953260525#u32,2029654566#u32,680895976#u32,2045700115#u32,55308719#u32,396423749#u32,1167628649#u32,360466872#u32,1754362792#u32,1666595357#u32,184794348#u32,339987395#u32,1903127532#u32,2046779719#u32,1790059455#u32,1540857739#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨11,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1991745807#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1991745807<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 2077422590#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2077422590<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 145562825#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 145562825<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 948690732#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 948690732<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 2104879446#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2104879446<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1296568824#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1296568824<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 804158412#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 804158412<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 680123620#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 680123620<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 118399103#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 118399103<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1069719268#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1069719268<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1953260525#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1953260525<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 2029654566#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2029654566<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 680895976#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 680895976<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 2045700115#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2045700115<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 55308719#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 55308719<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 396423749#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 396423749<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1167628649#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1167628649<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 360466872#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 360466872<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1754362792#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1754362792<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1666595357#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1666595357<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 184794348#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 184794348<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 339987395#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 339987395<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1903127532#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1903127532<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 2046779719#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2046779719<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1790059455#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1790059455<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1540857739#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1540857739<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨11,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨11,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨11,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JFr_TX2_Slot11_2
end
