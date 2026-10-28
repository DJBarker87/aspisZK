import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot07_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[251#u8,193#u8,218#u8,43#u8,220#u8,34#u8,7#u8,116#u8,115#u8,95#u8,154#u8,102#u8,114#u8,78#u8,37#u8,34#u8,100#u8,121#u8,53#u8,45#u8,249#u8,106#u8,124#u8,107#u8,192#u8,132#u8,190#u8,14#u8,247#u8,243#u8,142#u8,46#u8,112#u8,120#u8,102#u8,42#u8,193#u8,130#u8,55#u8,23#u8,139#u8,61#u8,54#u8,10#u8,79#u8,44#u8,197#u8,64#u8,146#u8,7#u8,154#u8,73#u8,115#u8,90#u8,170#u8,17#u8,244#u8,246#u8,181#u8,69#u8,154#u8,112#u8,155#u8,33#u8,17#u8,40#u8,38#u8,121#u8,218#u8,82#u8,121#u8,17#u8,63#u8,251#u8,144#u8,82#u8,205#u8,108#u8,155#u8,49#u8,252#u8,128#u8,71#u8,44#u8,92#u8,181#u8,251#u8,2#u8,230#u8,85#u8,106#u8,23#u8,177#u8,121#u8,181#u8,47#u8,200#u8,221#u8,138#u8,60#u8,34#u8,175#u8,36#u8,48#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [735756795#u32,1946624732#u32,1721393011#u32,572870258#u32,758479204#u32,1803315961#u32,247366848#u32,781120503#u32,711358576#u32,389513921#u32,171326859#u32,1086663759#u32,1234831250#u32,296376947#u32,1169553140#u32,563835034#u32,2032543761#u32,293163738#u32,1385233215#u32,832269517#u32,742883580#u32,50050396#u32,392844774#u32,800422321#u32,1015733704#u32,807710498#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 735756795#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 735756795<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1946624732#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1946624732<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1721393011#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1721393011<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 572870258#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 572870258<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 758479204#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 758479204<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1803315961#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1803315961<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 247366848#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 247366848<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 781120503#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 781120503<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 711358576#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 711358576<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 389513921#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 389513921<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 171326859#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 171326859<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1086663759#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1086663759<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1234831250#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1234831250<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 296376947#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 296376947<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1169553140#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1169553140<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 563835034#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 563835034<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 2032543761#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2032543761<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 293163738#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 293163738<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1385233215#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1385233215<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 832269517#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 832269517<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 742883580#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 742883580<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 50050396#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 50050396<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 392844774#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 392844774<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 800422321#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 800422321<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1015733704#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1015733704<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 807710498#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 807710498<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨7,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot07_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot07_1
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[150#u8,143#u8,224#u8,102#u8,145#u8,202#u8,202#u8,71#u8,185#u8,69#u8,42#u8,86#u8,168#u8,19#u8,66#u8,67#u8,116#u8,29#u8,228#u8,13#u8,210#u8,85#u8,158#u8,14#u8,127#u8,62#u8,227#u8,113#u8,192#u8,245#u8,103#u8,60#u8,146#u8,65#u8,40#u8,120#u8,240#u8,74#u8,14#u8,124#u8,162#u8,186#u8,37#u8,104#u8,144#u8,153#u8,107#u8,68#u8,24#u8,227#u8,61#u8,7#u8,44#u8,234#u8,112#u8,113#u8,182#u8,160#u8,82#u8,26#u8,84#u8,177#u8,18#u8,93#u8,192#u8,133#u8,206#u8,106#u8,107#u8,185#u8,143#u8,65#u8,188#u8,197#u8,160#u8,5#u8,69#u8,214#u8,32#u8,4#u8,6#u8,130#u8,216#u8,26#u8,116#u8,177#u8,28#u8,106#u8,151#u8,143#u8,122#u8,51#u8,219#u8,255#u8,176#u8,94#u8,150#u8,70#u8,242#u8,110#u8,133#u8,160#u8,186#u8,21#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1725992854#u32,1204472465#u32,1445610937#u32,1128403880#u32,233053556#u32,245257682#u32,1910718079#u32,1013446080#u32,2015904146#u32,2081311472#u32,1747303074#u32,1147902352#u32,121496344#u32,1903225388#u32,441622710#u32,1561506132#u32,1791919552#u32,1099938155#u32,94422460#u32,69260869#u32,450396678#u32,1780265332#u32,863670167#u32,1588658139#u32,1861371542#u32,364552325#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop 120).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 120 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1725992854#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1725992854<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1204472465#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1204472465<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1445610937#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1445610937<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1128403880#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1128403880<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 233053556#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 233053556<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 245257682#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 245257682<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1910718079#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1910718079<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1013446080#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1013446080<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 2015904146#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2015904146<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 2081311472#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2081311472<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1747303074#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1747303074<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1147902352#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1147902352<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 121496344#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 121496344<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1903225388#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1903225388<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 441622710#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 441622710<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1561506132#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1561506132<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1791919552#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1791919552<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1099938155#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1099938155<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 94422460#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 94422460<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 69260869#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 69260869<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 450396678#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 450396678<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1780265332#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1780265332<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 863670167#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 863670167<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1588658139#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1588658139<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1861371542#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1861371542<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 364552325#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 364552325<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
    1#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop (120*1+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨7,by decide⟩).val 120 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot07_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot07_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[209#u8,162#u8,206#u8,41#u8,39#u8,156#u8,245#u8,18#u8,175#u8,185#u8,43#u8,101#u8,225#u8,40#u8,143#u8,8#u8,63#u8,144#u8,39#u8,29#u8,210#u8,74#u8,224#u8,84#u8,57#u8,147#u8,221#u8,73#u8,230#u8,169#u8,88#u8,87#u8,62#u8,43#u8,28#u8,72#u8,157#u8,185#u8,136#u8,50#u8,11#u8,99#u8,211#u8,117#u8,207#u8,137#u8,45#u8,83#u8,62#u8,192#u8,109#u8,85#u8,11#u8,203#u8,204#u8,31#u8,145#u8,106#u8,127#u8,75#u8,11#u8,90#u8,83#u8,11#u8,16#u8,146#u8,52#u8,44#u8,34#u8,70#u8,202#u8,110#u8,162#u8,217#u8,68#u8,90#u8,15#u8,243#u8,11#u8,77#u8,19#u8,131#u8,70#u8,19#u8,78#u8,46#u8,143#u8,88#u8,135#u8,132#u8,255#u8,112#u8,199#u8,194#u8,198#u8,82#u8,197#u8,185#u8,79#u8,5#u8,70#u8,178#u8,20#u8,74#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [701407953#u32,318086183#u32,1697364399#u32,143599841#u32,489132095#u32,1423985362#u32,1239257913#u32,1465428454#u32,1209805630#u32,847821213#u32,1976787723#u32,1395493327#u32,1433255998#u32,533515019#u32,1266641553#u32,190011915#u32,741642768#u32,1858749986#u32,1514461602#u32,1292628751#u32,323388179#u32,1485778510#u32,1895793799#u32,1388757703#u32,89110981#u32,1242870342#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 701407953#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 701407953<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 318086183#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 318086183<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1697364399#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1697364399<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 143599841#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 143599841<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 489132095#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 489132095<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1423985362#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1423985362<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1239257913#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1239257913<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1465428454#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1465428454<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1209805630#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1209805630<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 847821213#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 847821213<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1976787723#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1976787723<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1395493327#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1395493327<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1433255998#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1433255998<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 533515019#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 533515019<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1266641553#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1266641553<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 190011915#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 190011915<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 741642768#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 741642768<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1858749986#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1858749986<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1514461602#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1514461602<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1292628751#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1292628751<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 323388179#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 323388179<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1485778510#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1485778510<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1895793799#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1895793799<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1388757703#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1388757703<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 89110981#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 89110981<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1242870342#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1242870342<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨7,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot07_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot07_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[57#u8,73#u8,38#u8,28#u8,173#u8,228#u8,228#u8,86#u8,226#u8,41#u8,236#u8,100#u8,52#u8,71#u8,201#u8,79#u8,110#u8,45#u8,87#u8,19#u8,175#u8,138#u8,239#u8,120#u8,225#u8,136#u8,23#u8,28#u8,112#u8,10#u8,159#u8,74#u8,92#u8,183#u8,120#u8,26#u8,233#u8,139#u8,232#u8,98#u8,54#u8,184#u8,115#u8,76#u8,65#u8,105#u8,150#u8,28#u8,17#u8,13#u8,128#u8,86#u8,103#u8,212#u8,212#u8,71#u8,187#u8,85#u8,189#u8,92#u8,111#u8,183#u8,92#u8,46#u8,117#u8,64#u8,168#u8,89#u8,36#u8,105#u8,103#u8,95#u8,13#u8,197#u8,111#u8,123#u8,109#u8,136#u8,118#u8,104#u8,233#u8,40#u8,10#u8,32#u8,233#u8,230#u8,107#u8,19#u8,46#u8,106#u8,152#u8,7#u8,105#u8,213#u8,56#u8,66#u8,80#u8,160#u8,88#u8,76#u8,216#u8,217#u8,101#u8,55#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [472271161#u32,1457841325#u32,1693198818#u32,1338591028#u32,324480366#u32,2028964527#u32,471304417#u32,1251936880#u32,444118876#u32,1659407337#u32,1282652214#u32,479619393#u32,1451232529#u32,1205130343#u32,1555912123#u32,777828207#u32,1504198773#u32,1600612644#u32,2070922509#u32,1752598637#u32,537536745#u32,325838569#u32,127429166#u32,1111020905#u32,1280876624#u32,929421784#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 472271161#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 472271161<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1457841325#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1457841325<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1693198818#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1693198818<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1338591028#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1338591028<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 324480366#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 324480366<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 2028964527#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2028964527<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 471304417#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 471304417<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1251936880#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1251936880<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 444118876#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 444118876<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1659407337#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1659407337<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1282652214#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1282652214<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 479619393#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 479619393<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1451232529#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1451232529<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1205130343#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1205130343<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1555912123#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1555912123<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 777828207#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 777828207<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1504198773#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1504198773<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1600612644#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1600612644<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 2070922509#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2070922509<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1752598637#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1752598637<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 537536745#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 537536745<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 325838569#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 325838569<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 127429166#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 127429166<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1111020905#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1111020905<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1280876624#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1280876624<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 929421784#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 929421784<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨7,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨7,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨7,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot07_3
end
