import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Slot14_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[151#u8,218#u8,195#u8,37#u8,78#u8,71#u8,92#u8,92#u8,84#u8,37#u8,240#u8,30#u8,25#u8,115#u8,225#u8,56#u8,62#u8,221#u8,70#u8,31#u8,227#u8,199#u8,72#u8,45#u8,206#u8,79#u8,46#u8,113#u8,136#u8,241#u8,78#u8,25#u8,178#u8,39#u8,201#u8,91#u8,211#u8,163#u8,94#u8,86#u8,254#u8,187#u8,102#u8,96#u8,8#u8,189#u8,15#u8,74#u8,84#u8,185#u8,24#u8,32#u8,152#u8,231#u8,104#u8,78#u8,244#u8,51#u8,49#u8,39#u8,162#u8,11#u8,92#u8,72#u8,207#u8,209#u8,140#u8,75#u8,32#u8,134#u8,231#u8,54#u8,41#u8,241#u8,43#u8,14#u8,185#u8,128#u8,57#u8,44#u8,139#u8,85#u8,124#u8,5#u8,70#u8,7#u8,192#u8,102#u8,20#u8,35#u8,29#u8,70#u8,65#u8,135#u8,78#u8,65#u8,159#u8,244#u8,163#u8,98#u8,61#u8,109#u8,108#u8,2#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [633592471#u32,1549551438#u32,519054676#u32,954299161#u32,524737854#u32,759744483#u32,1898860494#u32,424604040#u32,1539909554#u32,1449042899#u32,1617345534#u32,1242545416#u32,538491220#u32,1315497880#u32,657535988#u32,1213991842#u32,1267519951#u32,921142816#u32,237760809#u32,741966009#u32,92034443#u32,1723860806#u32,1176314644#u32,1095665473#u32,1654912159#u32,40660285#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨14,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 633592471#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 633592471<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1549551438#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1549551438<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 519054676#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 519054676<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 954299161#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 954299161<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 524737854#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 524737854<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 759744483#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 759744483<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1898860494#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1898860494<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 424604040#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 424604040<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1539909554#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1539909554<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1449042899#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1449042899<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1617345534#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1617345534<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1242545416#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1242545416<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 538491220#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 538491220<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1315497880#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1315497880<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 657535988#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 657535988<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1213991842#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1213991842<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1267519951#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1267519951<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 921142816#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 921142816<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 237760809#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 237760809<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 741966009#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 741966009<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 92034443#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 92034443<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1723860806#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1723860806<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1176314644#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1176314644<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1095665473#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1095665473<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1654912159#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1654912159<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 40660285#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 40660285<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨14,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨14,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨14,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JFr_TX2_Slot14_3
end
