import RPt_JFr_TX2_ScalarRead
import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot00_0
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[33#u8,175#u8,17#u8,109#u8,71#u8,177#u8,133#u8,100#u8,11#u8,18#u8,79#u8,40#u8,34#u8,127#u8,145#u8,34#u8,233#u8,129#u8,168#u8,110#u8,43#u8,149#u8,30#u8,65#u8,2#u8,43#u8,183#u8,94#u8,16#u8,53#u8,210#u8,82#u8,81#u8,190#u8,238#u8,73#u8,26#u8,166#u8,106#u8,76#u8,155#u8,49#u8,108#u8,3#u8,110#u8,108#u8,167#u8,71#u8,85#u8,136#u8,214#u8,14#u8,181#u8,110#u8,127#u8,68#u8,11#u8,240#u8,176#u8,53#u8,46#u8,16#u8,205#u8,18#u8,181#u8,81#u8,136#u8,105#u8,242#u8,71#u8,250#u8,113#u8,69#u8,16#u8,210#u8,16#u8,212#u8,32#u8,174#u8,26#u8,131#u8,19#u8,88#u8,60#u8,242#u8,161#u8,228#u8,20#u8,129#u8,243#u8,33#u8,75#u8,14#u8,14#u8,101#u8,122#u8,226#u8,139#u8,173#u8,114#u8,212#u8,146#u8,219#u8,61#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1829875489#u32,1686483271#u32,676270603#u32,579960610#u32,1856537065#u32,1092523307#u32,1589062402#u32,1389507856#u32,1240383057#u32,1282057754#u32,57422235#u32,1202154606#u32,248940629#u32,1149202101#u32,900788235#u32,315428910#u32,1770541493#u32,1912227826#u32,282202181#u32,447619284#u32,1012405123#u32,350527986#u32,1260516225#u32,2053443086#u32,1923976162#u32,1037800148#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop 0).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 0 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1829875489#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1829875489<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1686483271#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1686483271<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 676270603#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 676270603<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 579960610#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 579960610<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1856537065#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1856537065<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1092523307#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1092523307<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1589062402#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1589062402<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1389507856#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1389507856<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1240383057#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1240383057<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1282057754#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1282057754<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 57422235#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 57422235<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1202154606#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1202154606<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 248940629#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 248940629<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1149202101#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1149202101<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 900788235#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 900788235<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 315428910#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 315428910<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1770541493#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1770541493<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1912227826#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1912227826<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 282202181#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 282202181<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 447619284#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 447619284<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1012405123#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1012405123<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 350527986#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 350527986<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1260516225#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1260516225<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 2053443086#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2053443086<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1923976162#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1923976162<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1037800148#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1037800148<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨0,by decide⟩)
    0#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop (120*0+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨0,by decide⟩).val 0 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot00_0
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot00_1
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[18#u8,202#u8,152#u8,66#u8,204#u8,47#u8,240#u8,9#u8,87#u8,20#u8,112#u8,120#u8,183#u8,222#u8,203#u8,120#u8,71#u8,143#u8,105#u8,127#u8,208#u8,165#u8,160#u8,119#u8,98#u8,148#u8,43#u8,103#u8,84#u8,242#u8,10#u8,12#u8,3#u8,104#u8,247#u8,114#u8,114#u8,58#u8,70#u8,32#u8,40#u8,30#u8,231#u8,90#u8,151#u8,213#u8,217#u8,3#u8,160#u8,239#u8,217#u8,28#u8,21#u8,184#u8,232#u8,9#u8,227#u8,29#u8,88#u8,54#u8,59#u8,134#u8,228#u8,10#u8,55#u8,194#u8,109#u8,85#u8,117#u8,180#u8,104#u8,28#u8,173#u8,17#u8,86#u8,95#u8,255#u8,176#u8,40#u8,85#u8,20#u8,18#u8,41#u8,109#u8,234#u8,98#u8,190#u8,83#u8,221#u8,210#u8,215#u8,117#u8,62#u8,187#u8,124#u8,52#u8,35#u8,214#u8,55#u8,56#u8,174#u8,223#u8,228#u8,39#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1117309458#u32,166735820#u32,2020611159#u32,2026626743#u32,2137624391#u32,2007016912#u32,1730909282#u32,202043988#u32,1928816643#u32,541473394#u32,1525095976#u32,64607639#u32,484044704#u32,166246421#u32,911744483#u32,182748731#u32,1433256503#u32,476623989#u32,1599476141#u32,1428730111#u32,1831408148#u32,1404986090#u32,1977078493#u32,880589630#u32,943183395#u32,669310894#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop 120).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 120 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1117309458#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1117309458<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 166735820#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 166735820<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 2020611159#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2020611159<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 2026626743#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2026626743<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 2137624391#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2137624391<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 2007016912#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2007016912<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1730909282#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1730909282<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 202043988#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 202043988<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 1928816643#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1928816643<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 541473394#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 541473394<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1525095976#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1525095976<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 64607639#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 64607639<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 484044704#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 484044704<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 166246421#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 166246421<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 911744483#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 911744483<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 182748731#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 182748731<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1433256503#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1433256503<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 476623989#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 476623989<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 1599476141#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1599476141<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1428730111#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1428730111<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1831408148#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1831408148<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1404986090#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1404986090<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 1977078493#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1977078493<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 880589630#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 880589630<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 943183395#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 943183395<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 669310894#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 669310894<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨0,by decide⟩)
    1#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop (120*1+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨0,by decide⟩).val 120 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot00_1
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot00_2
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[38#u8,214#u8,10#u8,82#u8,132#u8,187#u8,211#u8,95#u8,70#u8,21#u8,247#u8,64#u8,192#u8,79#u8,127#u8,93#u8,201#u8,52#u8,125#u8,33#u8,228#u8,49#u8,41#u8,7#u8,185#u8,225#u8,69#u8,76#u8,183#u8,24#u8,138#u8,66#u8,233#u8,171#u8,165#u8,37#u8,225#u8,62#u8,171#u8,88#u8,131#u8,44#u8,137#u8,84#u8,11#u8,201#u8,98#u8,44#u8,60#u8,45#u8,122#u8,23#u8,202#u8,209#u8,138#u8,69#u8,159#u8,172#u8,14#u8,119#u8,76#u8,247#u8,78#u8,72#u8,15#u8,181#u8,13#u8,74#u8,176#u8,252#u8,105#u8,14#u8,26#u8,5#u8,86#u8,57#u8,168#u8,203#u8,187#u8,64#u8,129#u8,208#u8,215#u8,55#u8,186#u8,17#u8,104#u8,62#u8,186#u8,199#u8,117#u8,30#u8,162#u8,38#u8,138#u8,7#u8,111#u8,19#u8,222#u8,20#u8,135#u8,2#u8,117#u8,30#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1376441894#u32,1607711620#u32,1089934662#u32,1568624576#u32,561853641#u32,120140260#u32,1279648185#u32,1116346551#u32,631614441#u32,1487617761#u32,1418275971#u32,744671499#u32,393882940#u32,1166725578#u32,1997450399#u32,1213134668#u32,1242412303#u32,241826992#u32,961938714#u32,1086049192#u32,936890497#u32,1047007674#u32,511035322#u32,126494370#u32,350098287#u32,510984839#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop 240).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 240 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1376441894#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1376441894<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1607711620#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1607711620<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 1089934662#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1089934662<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 1568624576#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1568624576<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 561853641#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 561853641<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 120140260#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 120140260<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 1279648185#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1279648185<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1116346551#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1116346551<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 631614441#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 631614441<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1487617761#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1487617761<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1418275971#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1418275971<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 744671499#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 744671499<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 393882940#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 393882940<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1166725578#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1166725578<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 1997450399#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1997450399<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 1213134668#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1213134668<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 1242412303#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1242412303<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 241826992#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 241826992<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 961938714#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 961938714<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1086049192#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1086049192<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 936890497#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 936890497<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 1047007674#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1047007674<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 511035322#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 511035322<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 126494370#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 126494370<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 350098287#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 350098287<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 510984839#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 510984839<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨0,by decide⟩)
    2#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop (120*2+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨0,by decide⟩).val 240 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot00_2
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Slot00_3
open Aeneas Aeneas.Std Result

def raw : Array U8 104#usize := ⟨[184#u8,80#u8,124#u8,82#u8,153#u8,234#u8,214#u8,67#u8,86#u8,189#u8,72#u8,12#u8,90#u8,2#u8,113#u8,7#u8,180#u8,214#u8,162#u8,116#u8,229#u8,27#u8,65#u8,84#u8,54#u8,181#u8,72#u8,47#u8,38#u8,11#u8,108#u8,93#u8,50#u8,12#u8,212#u8,39#u8,211#u8,192#u8,161#u8,106#u8,148#u8,215#u8,89#u8,92#u8,50#u8,19#u8,159#u8,81#u8,68#u8,192#u8,101#u8,78#u8,204#u8,69#u8,250#u8,91#u8,141#u8,218#u8,107#u8,25#u8,246#u8,134#u8,216#u8,127#u8,34#u8,189#u8,216#u8,52#u8,105#u8,11#u8,200#u8,108#u8,183#u8,246#u8,66#u8,55#u8,128#u8,136#u8,250#u8,59#u8,99#u8,202#u8,35#u8,77#u8,180#u8,78#u8,220#u8,22#u8,58#u8,53#u8,100#u8,39#u8,83#u8,34#u8,123#u8,92#u8,149#u8,8#u8,22#u8,94#u8,175#u8,150#u8,176#u8,109#u8],by rfl⟩
def values : Array U32 26#usize := Array.make 26#usize [1383878840#u32,1138158233#u32,206093654#u32,124846682#u32,1956828852#u32,1413553125#u32,793294134#u32,1567361830#u32,668208178#u32,1788985555#u32,1549391764#u32,1369379634#u32,1315291204#u32,1543128524#u32,426498701#u32,2144896758#u32,886619426#u32,1825049449#u32,927135415#u32,1006274688#u32,1294191203#u32,383536820#u32,660878650#u32,1551573587#u32,1578502293#u32,1840289455#u32]

theorem selected : ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop 360).take 104=raw.val := by
  rw [JFr_TX2_Windows.selected _ 360 104 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof02.bytes,JFx_DataProof02.c00_length,JFx_DataProof02.c01_length,JFx_DataProof02.c02_length,JFx_DataProof02.c03_length,JFx_DataProof02.c04_length,JFx_DataProof02.c05_length,JFx_DataProof02.c06_length,JFx_DataProof02.c07_length,JFx_DataProof02.c08_length,JFx_DataProof02.c09_length,JFx_DataProof02.c10_length,JFx_DataProof02.c11_length,JFx_DataProof02.c12_length,JFx_DataProof02.c13_length,JFx_DataProof02.c14_length,JFx_DataProof02.c15_length,JFx_DataProof02.c16_length,JFx_DataProof02.c17_length,JFx_DataProof02.c18_length,JFx_DataProof02.c19_length,JFx_DataProof02.c20_length,JFx_DataProof02.c21_length,JFx_DataProof02.c22_length,JFx_DataProof02.c23_length,JFx_DataProof02.c24_length,JFx_DataProof02.c25_length,JFx_DataProof02.c26_length,JFx_DataProof02.c27_length,JFx_DataProof02.c28_length,JFx_DataProof02.c29_length,JFx_DataProof02.c30_length,JFx_DataProof02.c31_length,JFx_DataProof02.c32_length,JFx_DataProof02.c33_length,JFx_DataProof02.c34_length,JFx_DataProof02.c35_length,JFx_DataProof02.c36_length,JFx_DataProof02.c37_length,JFx_DataProof02.c38_length,JFx_DataProof02.c39_length,JFx_DataProof02.c40_length,JFx_DataProof02.c41_length,JFx_DataProof02.c42_length,JFx_DataProof02.c43_length,JFx_DataProof02.c44_length,JFx_DataProof02.c45_length,JFx_DataProof02.c46_length,JFx_DataProof02.c47_length,JFx_DataProof02.c48_length,JFx_DataProof02.c49_length,JFx_DataProof02.c50_length,JFx_DataProof02.c51_length,JFx_DataProof02.c52_length,JFx_DataProof02.c53_length,JFx_DataProof02.c54_length,JFx_DataProof02.c55_length,JFx_DataProof02.c56_length,JFx_DataProof02.c57_length,JFx_DataProof02.c58_length,JFx_DataProof02.c59_length,JFx_DataProof02.c60_length,JFx_DataProof02.c61_length,JFx_DataProof02.c62_length,JFx_DataProof02.c63_length,JFx_DataProof02.c64_length,JFx_DataProof02.c65_length,JFx_DataProof02.c66_length,JFx_DataProof02.c67_length,JFx_DataProof02.c68_length,JFx_DataProof02.c69_length,JFx_DataProof02.c70_length,JFx_DataProof02.c71_length,JFx_DataProof02.c72_length,JFx_DataProof02.c73_length,JFx_DataProof02.c74_length,JFx_DataProof02.c75_length,JFx_DataProof02.c76_length,JFx_DataProof02.c77_length,JFx_DataProof02.c78_length,JFx_DataProof02.c79_length,JFx_DataProof02.c80_length,JFx_DataProof02.c81_length,JFx_DataProof02.c82_length,JFx_DataProof02.c83_length,JFx_DataProof02.c84_length,JFx_DataProof02.c85_length,JFx_DataProof02.c86_length,JFx_DataProof02.c87_length,JFx_DataProof02.c88_length,JFx_DataProof02.c89_length,JFx_DataProof02.c90_length,JFx_DataProof02.c91_length,JFx_DataProof02.c92_length,JFx_DataProof02.c93_length,JFx_DataProof02.c94_length,JFx_DataProof02.c95_length,JFx_DataProof02.c96_length,JFx_DataProof02.c97_length,JFx_DataProof02.c98_length,JFx_DataProof02.c99_length,JFx_DataProof02.c100_length,JFx_DataProof02.c101_length,JFx_DataProof02.c102_length,JFx_DataProof02.c103_length,JFx_DataProof02.c104_length,JFx_DataProof02.c105_length,JFx_DataProof02.c106_length,JFx_DataProof02.c107_length,JFx_DataProof02.c108_length,JFx_DataProof02.c109_length,JFx_DataProof02.c110_length,JFx_DataProof02.c111_length,JFx_DataProof02.c112_length,JFx_DataProof02.c113_length,JFx_DataProof02.c114_length,JFx_DataProof02.c115_length,JFx_DataProof02.c116_length,JFx_DataProof02.c117_length,JFx_DataProof02.c118_length,JFx_DataProof02.c119_length,JFx_DataProof02.c120_length,JFx_DataProof02.c121_length,JFx_DataProof02.c122_length,JFx_DataProof02.c123_length,JFx_DataProof02.c124_length,JFx_DataProof02.c125_length,JFx_DataProof02.c126_length,JFx_DataProof02.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem decode00 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨0,by decide⟩)=ok (some 1383878840#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1383878840<2147483647;omega)
#print axioms decode00
theorem decode01 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨1,by decide⟩)=ok (some 1138158233#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1138158233<2147483647;omega)
#print axioms decode01
theorem decode02 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨2,by decide⟩)=ok (some 206093654#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 206093654<2147483647;omega)
#print axioms decode02
theorem decode03 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨3,by decide⟩)=ok (some 124846682#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 124846682<2147483647;omega)
#print axioms decode03
theorem decode04 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨4,by decide⟩)=ok (some 1956828852#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1956828852<2147483647;omega)
#print axioms decode04
theorem decode05 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨5,by decide⟩)=ok (some 1413553125#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1413553125<2147483647;omega)
#print axioms decode05
theorem decode06 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨6,by decide⟩)=ok (some 793294134#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 793294134<2147483647;omega)
#print axioms decode06
theorem decode07 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨7,by decide⟩)=ok (some 1567361830#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1567361830<2147483647;omega)
#print axioms decode07
theorem decode08 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨8,by decide⟩)=ok (some 668208178#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 668208178<2147483647;omega)
#print axioms decode08
theorem decode09 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨9,by decide⟩)=ok (some 1788985555#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1788985555<2147483647;omega)
#print axioms decode09
theorem decode10 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨10,by decide⟩)=ok (some 1549391764#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1549391764<2147483647;omega)
#print axioms decode10
theorem decode11 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨11,by decide⟩)=ok (some 1369379634#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1369379634<2147483647;omega)
#print axioms decode11
theorem decode12 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨12,by decide⟩)=ok (some 1315291204#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1315291204<2147483647;omega)
#print axioms decode12
theorem decode13 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨13,by decide⟩)=ok (some 1543128524#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1543128524<2147483647;omega)
#print axioms decode13
theorem decode14 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨14,by decide⟩)=ok (some 426498701#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 426498701<2147483647;omega)
#print axioms decode14
theorem decode15 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨15,by decide⟩)=ok (some 2144896758#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 2144896758<2147483647;omega)
#print axioms decode15
theorem decode16 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨16,by decide⟩)=ok (some 886619426#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 886619426<2147483647;omega)
#print axioms decode16
theorem decode17 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨17,by decide⟩)=ok (some 1825049449#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1825049449<2147483647;omega)
#print axioms decode17
theorem decode18 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨18,by decide⟩)=ok (some 927135415#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 927135415<2147483647;omega)
#print axioms decode18
theorem decode19 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨19,by decide⟩)=ok (some 1006274688#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1006274688<2147483647;omega)
#print axioms decode19
theorem decode20 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨20,by decide⟩)=ok (some 1294191203#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1294191203<2147483647;omega)
#print axioms decode20
theorem decode21 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨21,by decide⟩)=ok (some 383536820#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 383536820<2147483647;omega)
#print axioms decode21
theorem decode22 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨22,by decide⟩)=ok (some 660878650#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 660878650<2147483647;omega)
#print axioms decode22
theorem decode23 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨23,by decide⟩)=ok (some 1551573587#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1551573587<2147483647;omega)
#print axioms decode23
theorem decode24 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨24,by decide⟩)=ok (some 1578502293#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1578502293<2147483647;omega)
#print axioms decode24
theorem decode25 : FIp_DotDecode.field.M31.from_le_bytes (JFr_TX2_DecodeCell.cell raw ⟨25,by decide⟩)=ok (some 1840289455#u32) :=
  JFr_TX2_DecodeCell.source _ _ rfl (by change 1840289455<2147483647;omega)
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

theorem source (t : Fin 26) : JFr_TX2_ScalarRead.read (JFr_TX2_Windows.array ⟨0,by decide⟩)
    3#usize (Usize.ofNat t.val (by have := t.isLt;scalar_tac))=
      ok (values.val[t.val]'(by rw [values.property];exact t.isLt)) := by
  apply JFr_TX2_ScalarRead.source _ _ _ (by decide) (by exact t.isLt) (JFr_TX2_DecodeCell.cell raw t) _ _ (decode t)
  change ((JFr_TX2_Windows.array ⟨0,by decide⟩).val.drop (120*3+4*t.val)).take 4=_
  have h:=JFq_Range.nested (JFr_TX2_Windows.array ⟨0,by decide⟩).val 360 104 (4*t.val) 4 (by have := t.isLt;omega)
  rw [←h,selected]
  rfl

#print axioms selected
#print axioms decode
#print axioms source
end AspisR1.JGw_Slot00_3
end
