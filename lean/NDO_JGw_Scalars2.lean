import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot02_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[131#u8,97#u8,126#u8,127#u8,209#u8,174#u8,69#u8,78#u8,252#u8,96#u8,140#u8,93#u8,252#u8,252#u8,152#u8,107#u8,250#u8,208#u8,27#u8,123#u8,174#u8,216#u8,97#u8,127#u8,205#u8,119#u8,251#u8,47#u8,246#u8,42#u8,27#u8,21#u8,159#u8,66#u8,33#u8,60#u8,133#u8,98#u8,6#u8,13#u8,21#u8,103#u8,205#u8,104#u8,169#u8,187#u8,211#u8,34#u8,18#u8,40#u8,98#u8,71#u8,141#u8,189#u8,169#u8,120#u8,162#u8,192#u8,239#u8,99#u8,179#u8,44#u8,188#u8,65#u8,226#u8,227#u8,56#u8,127#u8,1#u8,136#u8,238#u8,71#u8,93#u8,54#u8,152#u8,88#u8,61#u8,10#u8,20#u8,87#u8,247#u8,4#u8,90#u8,97#u8,120#u8,226#u8,107#u8,98#u8,32#u8,123#u8,244#u8,54#u8,250#u8,130#u8,238#u8,4#u8,49#u8,51#u8,126#u8,38#u8,139#u8,180#u8,65#u8,96#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [2138988931#u32,1313189585#u32,1569480956#u32,1805188348#u32,2065420538#u32,2137118894#u32,805009357#u32,354102006#u32,1008812703#u32,218522245#u32,1758291733#u32,584301481#u32,1197615122#u32,2024390029#u32,1676656802#u32,1102851251#u32,2134434786#u32,1206814721#u32,1486370397#u32,1460931133#u32,1633289463#u32,1651237496#u32,921991968#u32,82739962#u32,645804849#u32,1614918795#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 2138988931#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2138988931<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1313189585#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1313189585<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1569480956#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1569480956<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1805188348#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1805188348<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 2065420538#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2065420538<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 2137118894#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2137118894<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 805009357#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 805009357<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 354102006#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 354102006<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1008812703#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1008812703<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 218522245#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 218522245<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1758291733#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1758291733<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 584301481#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 584301481<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1197615122#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1197615122<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 2024390029#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2024390029<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1676656802#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1676656802<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1102851251#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1102851251<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 2134434786#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2134434786<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1206814721#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1206814721<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1486370397#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1486370397<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1460931133#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1460931133<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1633289463#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1633289463<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1651237496#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1651237496<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 921991968#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 921991968<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 82739962#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 82739962<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 645804849#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 645804849<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1614918795#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1614918795<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨2,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨2,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot02_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot02_1
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[255#u8,96#u8,229#u8,28#u8,16#u8,242#u8,217#u8,97#u8,173#u8,203#u8,51#u8,64#u8,169#u8,114#u8,184#u8,59#u8,194#u8,111#u8,255#u8,3#u8,169#u8,201#u8,92#u8,13#u8,8#u8,94#u8,42#u8,104#u8,17#u8,128#u8,22#u8,123#u8,127#u8,28#u8,212#u8,104#u8,191#u8,2#u8,39#u8,85#u8,250#u8,40#u8,118#u8,96#u8,7#u8,49#u8,80#u8,124#u8,233#u8,118#u8,98#u8,8#u8,231#u8,160#u8,87#u8,33#u8,191#u8,115#u8,125#u8,94#u8,79#u8,93#u8,78#u8,30#u8,172#u8,156#u8,34#u8,33#u8,115#u8,31#u8,221#u8,68#u8,68#u8,107#u8,197#u8,125#u8,143#u8,120#u8,186#u8,110#u8,164#u8,51#u8,244#u8,52#u8,17#u8,158#u8,77#u8,127#u8,118#u8,178#u8,127#u8,2#u8,192#u8,204#u8,113#u8,53#u8,196#u8,9#u8,179#u8,70#u8,166#u8,220#u8,77#u8,99#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [484794623#u32,1641673232#u32,1077136301#u32,1001943721#u32,67071938#u32,224184745#u32,1747607048#u32,2065072145#u32,1758731391#u32,1428619967#u32,1618356474#u32,2085630215#u32,140670697#u32,559390951#u32,1585279935#u32,508452175#u32,555916460#u32,1155342195#u32,2110090052#u32,1857714319#u32,888419236#u32,2135793169#u32,41923190#u32,896650432#u32,1186138564#u32,1666047142#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop 120).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 120 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 484794623#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 484794623<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1641673232#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1641673232<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1077136301#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1077136301<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1001943721#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1001943721<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 67071938#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 67071938<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 224184745#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 224184745<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1747607048#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1747607048<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 2065072145#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2065072145<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1758731391#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1758731391<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1428619967#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1428619967<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1618356474#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1618356474<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 2085630215#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2085630215<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 140670697#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 140670697<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 559390951#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 559390951<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1585279935#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1585279935<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 508452175#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 508452175<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 555916460#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 555916460<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1155342195#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1155342195<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 2110090052#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2110090052<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1857714319#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1857714319<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 888419236#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 888419236<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 2135793169#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2135793169<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 41923190#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 41923190<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 896650432#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 896650432<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1186138564#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1186138564<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1666047142#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1666047142<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨2,by decide⟩)
    1#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop (120*1+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨2,by decide⟩).val 120 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot02_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot02_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[63#u8,60#u8,147#u8,58#u8,11#u8,184#u8,202#u8,73#u8,96#u8,130#u8,112#u8,116#u8,104#u8,190#u8,242#u8,5#u8,116#u8,106#u8,216#u8,76#u8,219#u8,45#u8,51#u8,13#u8,189#u8,207#u8,193#u8,22#u8,128#u8,31#u8,102#u8,66#u8,159#u8,99#u8,49#u8,73#u8,217#u8,133#u8,116#u8,98#u8,10#u8,92#u8,243#u8,124#u8,135#u8,10#u8,191#u8,91#u8,98#u8,238#u8,41#u8,53#u8,106#u8,155#u8,29#u8,85#u8,143#u8,72#u8,128#u8,121#u8,117#u8,17#u8,89#u8,79#u8,100#u8,2#u8,111#u8,51#u8,223#u8,61#u8,71#u8,66#u8,55#u8,152#u8,100#u8,126#u8,171#u8,118#u8,87#u8,104#u8,170#u8,30#u8,128#u8,76#u8,158#u8,53#u8,17#u8,97#u8,74#u8,129#u8,45#u8,18#u8,79#u8,206#u8,250#u8,24#u8,85#u8,132#u8,231#u8,24#u8,113#u8,173#u8,250#u8,57#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [982727743#u32,1238022155#u32,1953530464#u32,99794536#u32,1289251444#u32,221457883#u32,381800381#u32,1113988992#u32,1227973535#u32,1651803609#u32,2096323594#u32,1539246727#u32,891940450#u32,1428003690#u32,2038450319#u32,1331237237#u32,862913124#u32,1111965151#u32,2120521783#u32,1750562475#u32,1283464874#u32,1628517790#u32,304972106#u32,419089999#u32,417825877#u32,972729713#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 982727743#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 982727743<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1238022155#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1238022155<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1953530464#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1953530464<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 99794536#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 99794536<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1289251444#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1289251444<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 221457883#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 221457883<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 381800381#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 381800381<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1113988992#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1113988992<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1227973535#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1227973535<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1651803609#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1651803609<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 2096323594#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2096323594<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1539246727#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1539246727<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 891940450#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 891940450<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1428003690#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1428003690<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 2038450319#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2038450319<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1331237237#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1331237237<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 862913124#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 862913124<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1111965151#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1111965151<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 2120521783#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2120521783<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1750562475#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1750562475<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1283464874#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1283464874<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1628517790#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1628517790<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 304972106#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 304972106<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 419089999#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 419089999<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 417825877#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 417825877<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 972729713#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 972729713<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨2,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨2,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot02_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot02_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[199#u8,29#u8,210#u8,107#u8,98#u8,17#u8,59#u8,52#u8,255#u8,16#u8,45#u8,22#u8,26#u8,242#u8,174#u8,74#u8,202#u8,179#u8,163#u8,98#u8,238#u8,154#u8,50#u8,40#u8,7#u8,141#u8,15#u8,47#u8,7#u8,87#u8,55#u8,34#u8,138#u8,254#u8,160#u8,45#u8,47#u8,215#u8,72#u8,70#u8,172#u8,210#u8,132#u8,36#u8,196#u8,27#u8,168#u8,56#u8,134#u8,104#u8,156#u8,30#u8,163#u8,202#u8,207#u8,14#u8,124#u8,158#u8,17#u8,105#u8,106#u8,24#u8,193#u8,78#u8,202#u8,105#u8,255#u8,21#u8,35#u8,244#u8,215#u8,104#u8,59#u8,175#u8,67#u8,64#u8,61#u8,175#u8,253#u8,18#u8,190#u8,197#u8,140#u8,73#u8,38#u8,21#u8,31#u8,107#u8,201#u8,239#u8,43#u8,65#u8,205#u8,164#u8,170#u8,108#u8,198#u8,152#u8,98#u8,96#u8,194#u8,205#u8,134#u8,2#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1808932295#u32,876286306#u32,372052223#u32,1252979226#u32,1654895562#u32,674405102#u32,789548295#u32,574052103#u32,765525642#u32,1179178799#u32,612684460#u32,950541252#u32,513566854#u32,248498851#u32,1762762364#u32,1321277546#u32,369060298#u32,1758983203#u32,1078177595#u32,318615357#u32,1233962430#u32,1797199142#u32,1093398473#u32,1823122637#u32,1617074374#u32,42388930#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1808932295#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1808932295<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 876286306#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 876286306<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 372052223#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 372052223<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1252979226#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1252979226<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1654895562#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1654895562<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 674405102#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 674405102<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 789548295#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 789548295<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 574052103#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 574052103<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 765525642#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 765525642<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1179178799#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1179178799<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 612684460#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 612684460<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 950541252#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 950541252<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 513566854#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 513566854<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 248498851#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 248498851<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1762762364#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1762762364<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1321277546#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1321277546<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 369060298#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 369060298<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1758983203#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1758983203<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1078177595#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1078177595<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 318615357#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 318615357<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1233962430#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1233962430<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1797199142#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1797199142<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1093398473#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1093398473<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1823122637#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1823122637<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1617074374#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1617074374<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 42388930#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 42388930<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨2,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨2,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨2,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot02_3
end
