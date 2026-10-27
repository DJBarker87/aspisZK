import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_Slot13_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[22#u8,111#u8,140#u8,16#u8,237#u8,250#u8,146#u8,38#u8,22#u8,37#u8,199#u8,114#u8,177#u8,66#u8,90#u8,51#u8,6#u8,149#u8,79#u8,36#u8,92#u8,32#u8,133#u8,55#u8,125#u8,32#u8,165#u8,81#u8,130#u8,17#u8,169#u8,27#u8,197#u8,234#u8,127#u8,88#u8,129#u8,123#u8,209#u8,21#u8,42#u8,53#u8,191#u8,40#u8,203#u8,158#u8,36#u8,26#u8,167#u8,210#u8,226#u8,80#u8,44#u8,227#u8,183#u8,8#u8,217#u8,5#u8,228#u8,127#u8,97#u8,227#u8,23#u8,9#u8,81#u8,255#u8,226#u8,103#u8,122#u8,121#u8,101#u8,107#u8,73#u8,50#u8,214#u8,28#u8,80#u8,136#u8,190#u8,46#u8,235#u8,168#u8,23#u8,22#u8,154#u8,156#u8,112#u8,123#u8,144#u8,88#u8,61#u8,11#u8,83#u8,99#u8,133#u8,75#u8,61#u8,14#u8,91#u8,40#u8,102#u8,88#u8,77#u8,62#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [277638934#u32,647166701#u32,1925653782#u32,861553329#u32,609195270#u32,931471452#u32,1369776253#u32,464064898#u32,1484778181#u32,366050177#u32,683619626#u32,438607563#u32,1357042343#u32,146268972#u32,2145650137#u32,152560481#u32,1742929745#u32,1801812346#u32,483799625#u32,784238672#u32,370649323#u32,2070977690#u32,188569744#u32,1267032915#u32,677056061#u32,1045256294#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨13,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 277638934#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 277638934<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 647166701#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 647166701<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1925653782#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1925653782<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 861553329#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 861553329<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 609195270#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 609195270<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 931471452#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 931471452<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1369776253#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1369776253<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 464064898#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 464064898<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1484778181#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1484778181<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 366050177#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 366050177<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 683619626#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 683619626<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 438607563#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 438607563<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1357042343#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1357042343<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 146268972#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 146268972<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 2145650137#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2145650137<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 152560481#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 152560481<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1742929745#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1742929745<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1801812346#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1801812346<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 483799625#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 483799625<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 784238672#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 784238672<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 370649323#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 370649323<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 2070977690#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2070977690<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 188569744#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 188569744<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1267032915#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1267032915<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 677056061#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 677056061<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1045256294#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1045256294<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨13,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨13,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨13,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JFr_TX2_Slot13_0
end
