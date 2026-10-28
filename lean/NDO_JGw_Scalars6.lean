import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot06_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[20#u8,93#u8,134#u8,56#u8,220#u8,125#u8,118#u8,10#u8,226#u8,130#u8,156#u8,16#u8,97#u8,52#u8,50#u8,125#u8,22#u8,87#u8,182#u8,67#u8,74#u8,88#u8,72#u8,0#u8,143#u8,105#u8,67#u8,55#u8,166#u8,176#u8,67#u8,121#u8,99#u8,27#u8,122#u8,102#u8,27#u8,233#u8,241#u8,24#u8,147#u8,246#u8,244#u8,96#u8,161#u8,134#u8,207#u8,5#u8,60#u8,235#u8,76#u8,50#u8,68#u8,25#u8,80#u8,72#u8,142#u8,84#u8,145#u8,8#u8,45#u8,6#u8,159#u8,111#u8,42#u8,254#u8,170#u8,75#u8,182#u8,103#u8,228#u8,121#u8,198#u8,50#u8,0#u8,100#u8,228#u8,27#u8,240#u8,80#u8,249#u8,233#u8,65#u8,98#u8,221#u8,237#u8,126#u8,100#u8,43#u8,156#u8,141#u8,52#u8,130#u8,25#u8,210#u8,92#u8,88#u8,167#u8,91#u8,119#u8,96#u8,155#u8,72#u8,29#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [948329748#u32,175537628#u32,278692578#u32,2100442209#u32,1136023318#u32,4741194#u32,927164815#u32,2034479270#u32,1719278435#u32,418507035#u32,1626666643#u32,97486497#u32,843901756#u32,1213208900#u32,143742094#u32,1872692781#u32,1269497386#u32,2045011894#u32,1677734598#u32,1357913060#u32,1648486905#u32,1686040029#u32,881695787#u32,1557272962#u32,2002495320#u32,491297632#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 948329748#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 948329748<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 175537628#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 175537628<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 278692578#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 278692578<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 2100442209#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2100442209<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1136023318#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1136023318<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 4741194#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 4741194<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 927164815#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 927164815<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 2034479270#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2034479270<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1719278435#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1719278435<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 418507035#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 418507035<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1626666643#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1626666643<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 97486497#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 97486497<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 843901756#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 843901756<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1213208900#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1213208900<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 143742094#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 143742094<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1872692781#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1872692781<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1269497386#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1269497386<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 2045011894#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2045011894<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1677734598#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1677734598<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1357913060#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1357913060<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1648486905#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1648486905<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1686040029#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1686040029<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 881695787#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 881695787<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1557272962#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1557272962<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 2002495320#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2002495320<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 491297632#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 491297632<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨6,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot06_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot06_1
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[174#u8,15#u8,179#u8,17#u8,90#u8,201#u8,70#u8,88#u8,233#u8,205#u8,126#u8,59#u8,119#u8,96#u8,79#u8,97#u8,179#u8,239#u8,31#u8,73#u8,146#u8,236#u8,32#u8,74#u8,238#u8,14#u8,42#u8,25#u8,39#u8,129#u8,8#u8,15#u8,141#u8,104#u8,222#u8,23#u8,30#u8,94#u8,43#u8,34#u8,114#u8,6#u8,148#u8,91#u8,182#u8,101#u8,45#u8,8#u8,90#u8,146#u8,243#u8,3#u8,3#u8,92#u8,124#u8,45#u8,175#u8,194#u8,158#u8,26#u8,45#u8,207#u8,49#u8,94#u8,110#u8,199#u8,80#u8,69#u8,30#u8,79#u8,59#u8,22#u8,157#u8,233#u8,230#u8,115#u8,81#u8,68#u8,138#u8,60#u8,122#u8,185#u8,248#u8,10#u8,66#u8,37#u8,253#u8,27#u8,223#u8,114#u8,55#u8,100#u8,25#u8,215#u8,240#u8,59#u8,37#u8,133#u8,67#u8,47#u8,25#u8,242#u8,244#u8,30#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [296947630#u32,1481034074#u32,998165993#u32,1632591991#u32,1226829747#u32,1243671698#u32,422186734#u32,252215591#u32,400451725#u32,573267486#u32,1536427634#u32,137192886#u32,66294362#u32,763124739#u32,446612143#u32,1580322605#u32,1162921838#u32,372985630#u32,1944512925#u32,1015694417#u32,184072570#u32,469574978#u32,1681355487#u32,1005639449#u32,792954149#u32,519369241#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop 120).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 120 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 296947630#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 296947630<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1481034074#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1481034074<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 998165993#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 998165993<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1632591991#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1632591991<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1226829747#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1226829747<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1243671698#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1243671698<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 422186734#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 422186734<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 252215591#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 252215591<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 400451725#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 400451725<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 573267486#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 573267486<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1536427634#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1536427634<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 137192886#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 137192886<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 66294362#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 66294362<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 763124739#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 763124739<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 446612143#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 446612143<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1580322605#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1580322605<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1162921838#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1162921838<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 372985630#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 372985630<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1944512925#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1944512925<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1015694417#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1015694417<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 184072570#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 184072570<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 469574978#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 469574978<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1681355487#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1681355487<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1005639449#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1005639449<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 792954149#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 792954149<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 519369241#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 519369241<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
    1#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop (120*1+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨6,by decide⟩).val 120 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot06_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot06_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[103#u8,184#u8,14#u8,105#u8,173#u8,254#u8,82#u8,10#u8,104#u8,162#u8,153#u8,2#u8,99#u8,103#u8,255#u8,125#u8,72#u8,63#u8,98#u8,29#u8,38#u8,170#u8,17#u8,62#u8,59#u8,223#u8,226#u8,98#u8,223#u8,157#u8,245#u8,53#u8,240#u8,85#u8,223#u8,58#u8,234#u8,52#u8,209#u8,76#u8,25#u8,18#u8,138#u8,7#u8,115#u8,63#u8,185#u8,80#u8,116#u8,150#u8,124#u8,83#u8,172#u8,239#u8,0#u8,41#u8,29#u8,41#u8,136#u8,3#u8,181#u8,123#u8,127#u8,67#u8,82#u8,45#u8,146#u8,84#u8,215#u8,115#u8,252#u8,119#u8,79#u8,38#u8,202#u8,23#u8,191#u8,222#u8,172#u8,106#u8,62#u8,214#u8,142#u8,83#u8,183#u8,215#u8,153#u8,1#u8,112#u8,159#u8,138#u8,67#u8,203#u8,164#u8,128#u8,11#u8,51#u8,30#u8,65#u8,14#u8,51#u8,229#u8,14#u8,102#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1762572391#u32,173211309#u32,43623016#u32,2113890147#u32,492977992#u32,1041345062#u32,1659035451#u32,905289183#u32,987715056#u32,1288778986#u32,126489113#u32,1354317683#u32,1400673908#u32,687927212#u32,59255069#u32,1132428213#u32,1418866002#u32,2013033431#u32,399124047#u32,1789714111#u32,1401869886#u32,26859447#u32,1133158256#u32,192980171#u32,239148595#u32,1712252211#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1762572391#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1762572391<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 173211309#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 173211309<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 43623016#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 43623016<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 2113890147#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2113890147<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 492977992#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 492977992<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1041345062#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1041345062<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1659035451#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1659035451<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 905289183#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 905289183<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 987715056#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 987715056<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1288778986#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1288778986<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 126489113#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 126489113<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1354317683#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1354317683<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1400673908#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1400673908<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 687927212#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 687927212<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 59255069#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 59255069<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1132428213#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1132428213<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1418866002#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1418866002<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 2013033431#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2013033431<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 399124047#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 399124047<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1789714111#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1789714111<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1401869886#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1401869886<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 26859447#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 26859447<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1133158256#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1133158256<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 192980171#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 192980171<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 239148595#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 239148595<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1712252211#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1712252211<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨6,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot06_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot06_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[47#u8,37#u8,98#u8,6#u8,58#u8,57#u8,14#u8,34#u8,203#u8,200#u8,78#u8,15#u8,200#u8,206#u8,74#u8,24#u8,119#u8,163#u8,73#u8,82#u8,236#u8,63#u8,131#u8,117#u8,182#u8,57#u8,9#u8,40#u8,75#u8,127#u8,65#u8,43#u8,54#u8,185#u8,141#u8,102#u8,199#u8,102#u8,35#u8,116#u8,48#u8,216#u8,128#u8,105#u8,220#u8,173#u8,77#u8,82#u8,72#u8,34#u8,144#u8,30#u8,254#u8,236#u8,12#u8,7#u8,151#u8,233#u8,45#u8,93#u8,116#u8,2#u8,9#u8,49#u8,112#u8,4#u8,70#u8,27#u8,233#u8,100#u8,108#u8,36#u8,173#u8,220#u8,169#u8,78#u8,255#u8,135#u8,66#u8,30#u8,233#u8,241#u8,112#u8,78#u8,0#u8,43#u8,141#u8,31#u8,152#u8,91#u8,151#u8,12#u8,109#u8,185#u8,181#u8,47#u8,66#u8,43#u8,67#u8,106#u8,159#u8,8#u8,31#u8,48#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [107095343#u32,571357498#u32,256821451#u32,407555784#u32,1380557687#u32,1971535852#u32,671693238#u32,725712715#u32,1720564022#u32,1948477127#u32,1770051632#u32,1380822492#u32,512762440#u32,118287614#u32,1563290007#u32,822674036#u32,457573488#u32,611083497#u32,1319754925#u32,507676671#u32,1316024809#u32,529345280#u32,211245976#u32,800438637#u32,1782786882#u32,807340191#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof03.bytes,JFx_DataProof03.c00_length,JFx_DataProof03.c01_length,JFx_DataProof03.c02_length,JFx_DataProof03.c03_length,JFx_DataProof03.c04_length,JFx_DataProof03.c05_length,JFx_DataProof03.c06_length,JFx_DataProof03.c07_length,JFx_DataProof03.c08_length,JFx_DataProof03.c09_length,JFx_DataProof03.c10_length,JFx_DataProof03.c11_length,JFx_DataProof03.c12_length,JFx_DataProof03.c13_length,JFx_DataProof03.c14_length,JFx_DataProof03.c15_length,JFx_DataProof03.c16_length,JFx_DataProof03.c17_length,JFx_DataProof03.c18_length,JFx_DataProof03.c19_length,JFx_DataProof03.c20_length,JFx_DataProof03.c21_length,JFx_DataProof03.c22_length,JFx_DataProof03.c23_length,JFx_DataProof03.c24_length,JFx_DataProof03.c25_length,JFx_DataProof03.c26_length,JFx_DataProof03.c27_length,JFx_DataProof03.c28_length,JFx_DataProof03.c29_length,JFx_DataProof03.c30_length,JFx_DataProof03.c31_length,JFx_DataProof03.c32_length,JFx_DataProof03.c33_length,JFx_DataProof03.c34_length,JFx_DataProof03.c35_length,JFx_DataProof03.c36_length,JFx_DataProof03.c37_length,JFx_DataProof03.c38_length,JFx_DataProof03.c39_length,JFx_DataProof03.c40_length,JFx_DataProof03.c41_length,JFx_DataProof03.c42_length,JFx_DataProof03.c43_length,JFx_DataProof03.c44_length,JFx_DataProof03.c45_length,JFx_DataProof03.c46_length,JFx_DataProof03.c47_length,JFx_DataProof03.c48_length,JFx_DataProof03.c49_length,JFx_DataProof03.c50_length,JFx_DataProof03.c51_length,JFx_DataProof03.c52_length,JFx_DataProof03.c53_length,JFx_DataProof03.c54_length,JFx_DataProof03.c55_length,JFx_DataProof03.c56_length,JFx_DataProof03.c57_length,JFx_DataProof03.c58_length,JFx_DataProof03.c59_length,JFx_DataProof03.c60_length,JFx_DataProof03.c61_length,JFx_DataProof03.c62_length,JFx_DataProof03.c63_length,JFx_DataProof03.c64_length,JFx_DataProof03.c65_length,JFx_DataProof03.c66_length,JFx_DataProof03.c67_length,JFx_DataProof03.c68_length,JFx_DataProof03.c69_length,JFx_DataProof03.c70_length,JFx_DataProof03.c71_length,JFx_DataProof03.c72_length,JFx_DataProof03.c73_length,JFx_DataProof03.c74_length,JFx_DataProof03.c75_length,JFx_DataProof03.c76_length,JFx_DataProof03.c77_length,JFx_DataProof03.c78_length,JFx_DataProof03.c79_length,JFx_DataProof03.c80_length,JFx_DataProof03.c81_length,JFx_DataProof03.c82_length,JFx_DataProof03.c83_length,JFx_DataProof03.c84_length,JFx_DataProof03.c85_length,JFx_DataProof03.c86_length,JFx_DataProof03.c87_length,JFx_DataProof03.c88_length,JFx_DataProof03.c89_length,JFx_DataProof03.c90_length,JFx_DataProof03.c91_length,JFx_DataProof03.c92_length,JFx_DataProof03.c93_length,JFx_DataProof03.c94_length,JFx_DataProof03.c95_length,JFx_DataProof03.c96_length,JFx_DataProof03.c97_length,JFx_DataProof03.c98_length,JFx_DataProof03.c99_length,JFx_DataProof03.c100_length,JFx_DataProof03.c101_length,JFx_DataProof03.c102_length,JFx_DataProof03.c103_length,JFx_DataProof03.c104_length,JFx_DataProof03.c105_length,JFx_DataProof03.c106_length,JFx_DataProof03.c107_length,JFx_DataProof03.c108_length,JFx_DataProof03.c109_length,JFx_DataProof03.c110_length,JFx_DataProof03.c111_length,JFx_DataProof03.c112_length,JFx_DataProof03.c113_length,JFx_DataProof03.c114_length,JFx_DataProof03.c115_length,JFx_DataProof03.c116_length,JFx_DataProof03.c117_length,JFx_DataProof03.c118_length,JFx_DataProof03.c119_length,JFx_DataProof03.c120_length,JFx_DataProof03.c121_length,JFx_DataProof03.c122_length,JFx_DataProof03.c123_length,JFx_DataProof03.c124_length,JFx_DataProof03.c125_length,JFx_DataProof03.c126_length,JFx_DataProof03.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 107095343#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 107095343<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 571357498#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 571357498<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 256821451#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 256821451<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 407555784#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 407555784<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1380557687#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1380557687<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1971535852#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1971535852<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 671693238#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 671693238<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 725712715#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 725712715<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1720564022#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1720564022<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1948477127#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1948477127<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1770051632#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1770051632<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1380822492#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1380822492<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 512762440#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 512762440<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 118287614#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 118287614<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1563290007#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1563290007<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 822674036#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 822674036<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 457573488#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 457573488<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 611083497#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 611083497<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1319754925#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1319754925<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 507676671#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 507676671<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1316024809#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1316024809<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 529345280#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 529345280<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 211245976#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 211245976<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 800438637#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 800438637<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1782786882#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1782786882<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 807340191#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 807340191<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨6,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨6,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨6,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot06_3
end
