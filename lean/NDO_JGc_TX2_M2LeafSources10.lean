import RPt_JFn_Value10_0
import RPt_JFn_Value10_1
import RPt_JFn_Value10_2
import RPt_JFn_Value10_3
import RPt_JFn_Value11_0
import RPt_JFn_Value11_1
import RPt_JFn_Value11_2
import RPt_JFn_Value11_3
import RPt_JFn_Value12_0
import RPt_JFn_Value12_1
import RPt_JFn_Value12_2
import RPt_JFn_Value12_3
import RPt_JFn_Value13_0
import RPt_JFn_Value13_1
import RPt_JFn_Value13_2
import RPt_JFn_Value13_3
import NDO_JGc_TX2_LeafHelpers
import NDO_JGc_TX2_M2Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf10
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value10_0.bytes
def n0 : List Nat := [175,11,41,89,203,237,204,33,130,196,3,49,177,192,179,78,95,15,32,86,1,15,63,80,26,23,138,62,236,64,44,52]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value10_1.bytes
def n1 : List Nat := [157,31,202,6,199,199,88,5,143,36,99,47,16,254,243,125,5,213,144,76,235,219,47,37,54,51,106,47,191,166,251,90]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value10_2.bytes
def n2 : List Nat := [54,220,67,4,43,217,23,127,196,33,243,81,95,27,224,62,126,58,108,11,86,227,253,3,28,175,173,32,121,24,97,36]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value10_3.bytes
def n3 : List Nat := [55,55,228,120,120,13,137,48,241,107,27,21,41,228,7,82,90,171,226,97,152,141,60,125,57,177,80,1,208,228,130,95]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [74#u8,77#u8,212#u8,235#u8,211#u8,95#u8,63#u8,45#u8,224#u8,243#u8,105#u8,67#u8,143#u8,249#u8,74#u8,213#u8,202#u8,137#u8,236#u8,93#u8,23#u8,120#u8,127#u8,211#u8,52#u8,124#u8,55#u8,204#u8,207#u8,128#u8,89#u8,212#u8]
def n4 : List Nat := [74,77,212,235,211,95,63,45,224,243,105,67,143,249,74,213,202,137,236,93,23,120,127,211,52,124,55,204,207,128,89,212]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨10,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨10,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨10,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value10_0.selected JFn_Value10_1.selected JFn_Value10_2.selected JFn_Value10_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash000.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash000.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash000.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash000.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash000.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash000.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash000.message,JGc_TX2_M2.Hash000.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨10,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash000.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨10,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨10,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨10,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value000) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨10,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨10,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨10,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash000.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf10
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf11
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value11_0.bytes
def n0 : List Nat := [178,173,1,56,222,154,223,1,186,133,135,41,149,132,121,18,129,228,247,72,119,43,239,36,239,161,21,72,69,127,26,114]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value11_1.bytes
def n1 : List Nat := [56,95,250,124,96,33,4,58,92,93,130,3,90,12,168,52,142,80,190,118,150,186,34,84,39,151,129,71,166,53,42,55]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value11_2.bytes
def n2 : List Nat := [128,103,193,0,74,181,74,74,125,213,245,6,153,193,191,54,209,203,157,59,248,229,22,4,108,49,48,1,70,131,193,111]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value11_3.bytes
def n3 : List Nat := [225,8,250,125,42,24,38,28,249,88,196,112,159,225,29,90,57,183,231,17,255,236,62,74,236,70,252,63,39,90,208,124]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [186#u8,73#u8,199#u8,106#u8,34#u8,144#u8,244#u8,214#u8,126#u8,37#u8,161#u8,188#u8,123#u8,106#u8,193#u8,59#u8,73#u8,99#u8,241#u8,116#u8,203#u8,144#u8,136#u8,131#u8,53#u8,249#u8,108#u8,44#u8,228#u8,138#u8,188#u8,6#u8]
def n4 : List Nat := [186,73,199,106,34,144,244,214,126,37,161,188,123,106,193,59,73,99,241,116,203,144,136,131,53,249,108,44,228,138,188,6]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨11,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof04.bytes,JFx_DataProof04.c00_length,JFx_DataProof04.c01_length,JFx_DataProof04.c02_length,JFx_DataProof04.c03_length,JFx_DataProof04.c04_length,JFx_DataProof04.c05_length,JFx_DataProof04.c06_length,JFx_DataProof04.c07_length,JFx_DataProof04.c08_length,JFx_DataProof04.c09_length,JFx_DataProof04.c10_length,JFx_DataProof04.c11_length,JFx_DataProof04.c12_length,JFx_DataProof04.c13_length,JFx_DataProof04.c14_length,JFx_DataProof04.c15_length,JFx_DataProof04.c16_length,JFx_DataProof04.c17_length,JFx_DataProof04.c18_length,JFx_DataProof04.c19_length,JFx_DataProof04.c20_length,JFx_DataProof04.c21_length,JFx_DataProof04.c22_length,JFx_DataProof04.c23_length,JFx_DataProof04.c24_length,JFx_DataProof04.c25_length,JFx_DataProof04.c26_length,JFx_DataProof04.c27_length,JFx_DataProof04.c28_length,JFx_DataProof04.c29_length,JFx_DataProof04.c30_length,JFx_DataProof04.c31_length,JFx_DataProof04.c32_length,JFx_DataProof04.c33_length,JFx_DataProof04.c34_length,JFx_DataProof04.c35_length,JFx_DataProof04.c36_length,JFx_DataProof04.c37_length,JFx_DataProof04.c38_length,JFx_DataProof04.c39_length,JFx_DataProof04.c40_length,JFx_DataProof04.c41_length,JFx_DataProof04.c42_length,JFx_DataProof04.c43_length,JFx_DataProof04.c44_length,JFx_DataProof04.c45_length,JFx_DataProof04.c46_length,JFx_DataProof04.c47_length,JFx_DataProof04.c48_length,JFx_DataProof04.c49_length,JFx_DataProof04.c50_length,JFx_DataProof04.c51_length,JFx_DataProof04.c52_length,JFx_DataProof04.c53_length,JFx_DataProof04.c54_length,JFx_DataProof04.c55_length,JFx_DataProof04.c56_length,JFx_DataProof04.c57_length,JFx_DataProof04.c58_length,JFx_DataProof04.c59_length,JFx_DataProof04.c60_length,JFx_DataProof04.c61_length,JFx_DataProof04.c62_length,JFx_DataProof04.c63_length,JFx_DataProof04.c64_length,JFx_DataProof04.c65_length,JFx_DataProof04.c66_length,JFx_DataProof04.c67_length,JFx_DataProof04.c68_length,JFx_DataProof04.c69_length,JFx_DataProof04.c70_length,JFx_DataProof04.c71_length,JFx_DataProof04.c72_length,JFx_DataProof04.c73_length,JFx_DataProof04.c74_length,JFx_DataProof04.c75_length,JFx_DataProof04.c76_length,JFx_DataProof04.c77_length,JFx_DataProof04.c78_length,JFx_DataProof04.c79_length,JFx_DataProof04.c80_length,JFx_DataProof04.c81_length,JFx_DataProof04.c82_length,JFx_DataProof04.c83_length,JFx_DataProof04.c84_length,JFx_DataProof04.c85_length,JFx_DataProof04.c86_length,JFx_DataProof04.c87_length,JFx_DataProof04.c88_length,JFx_DataProof04.c89_length,JFx_DataProof04.c90_length,JFx_DataProof04.c91_length,JFx_DataProof04.c92_length,JFx_DataProof04.c93_length,JFx_DataProof04.c94_length,JFx_DataProof04.c95_length,JFx_DataProof04.c96_length,JFx_DataProof04.c97_length,JFx_DataProof04.c98_length,JFx_DataProof04.c99_length,JFx_DataProof04.c100_length,JFx_DataProof04.c101_length,JFx_DataProof04.c102_length,JFx_DataProof04.c103_length,JFx_DataProof04.c104_length,JFx_DataProof04.c105_length,JFx_DataProof04.c106_length,JFx_DataProof04.c107_length,JFx_DataProof04.c108_length,JFx_DataProof04.c109_length,JFx_DataProof04.c110_length,JFx_DataProof04.c111_length,JFx_DataProof04.c112_length,JFx_DataProof04.c113_length,JFx_DataProof04.c114_length,JFx_DataProof04.c115_length,JFx_DataProof04.c116_length,JFx_DataProof04.c117_length,JFx_DataProof04.c118_length,JFx_DataProof04.c119_length,JFx_DataProof04.c120_length,JFx_DataProof04.c121_length,JFx_DataProof04.c122_length,JFx_DataProof04.c123_length,JFx_DataProof04.c124_length,JFx_DataProof04.c125_length,JFx_DataProof04.c126_length,JFx_DataProof04.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨11,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨11,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value11_0.selected JFn_Value11_1.selected JFn_Value11_2.selected JFn_Value11_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash001.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash001.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash001.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash001.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash001.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash001.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash001.message,JGc_TX2_M2.Hash001.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨11,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash001.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨11,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨11,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨11,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value001) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨11,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨11,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨11,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash001.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf11
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf12
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value12_0.bytes
def n0 : List Nat := [103,195,172,73,250,171,207,109,119,180,117,64,143,91,110,123,157,76,189,25,238,209,229,77,226,242,129,119,212,26,124,106]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value12_1.bytes
def n1 : List Nat := [165,142,109,26,184,223,65,82,13,251,117,113,13,33,230,60,245,96,5,10,206,33,235,96,179,5,128,92,11,2,22,112]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value12_2.bytes
def n2 : List Nat := [151,60,231,82,108,176,210,41,71,253,7,93,124,250,86,58,142,234,40,21,143,77,189,80,177,57,12,41,146,243,128,49]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value12_3.bytes
def n3 : List Nat := [95,91,104,35,138,156,53,35,66,80,241,97,88,229,234,50,45,112,251,124,202,214,105,97,121,220,156,73,97,5,185,99]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [201#u8,51#u8,197#u8,150#u8,99#u8,12#u8,131#u8,247#u8,132#u8,66#u8,173#u8,66#u8,37#u8,195#u8,229#u8,82#u8,10#u8,144#u8,154#u8,195#u8,103#u8,208#u8,143#u8,125#u8,120#u8,241#u8,137#u8,68#u8,218#u8,137#u8,106#u8,135#u8]
def n4 : List Nat := [201,51,197,150,99,12,131,247,132,66,173,66,37,195,229,82,10,144,154,195,103,208,143,125,120,241,137,68,218,137,106,135]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨12,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨12,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨12,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value12_0.selected JFn_Value12_1.selected JFn_Value12_2.selected JFn_Value12_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash002.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash002.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash002.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash002.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash002.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash002.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash002.message,JGc_TX2_M2.Hash002.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨12,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash002.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨12,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨12,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨12,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value002) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨12,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨12,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨12,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash002.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf12
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf13
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value13_0.bytes
def n0 : List Nat := [252,50,185,53,131,67,136,17,4,41,205,19,191,44,172,127,110,74,47,96,249,62,253,4,163,169,114,80,23,234,92,121]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value13_1.bytes
def n1 : List Nat := [58,13,141,35,121,245,75,79,196,13,139,35,131,157,131,113,70,3,127,61,186,191,34,108,105,8,53,50,23,118,14,21]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value13_2.bytes
def n2 : List Nat := [24,100,158,47,245,64,172,112,42,113,206,92,36,185,163,0,18,33,29,20,117,134,127,5,241,229,213,114,48,57,8,127]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value13_3.bytes
def n3 : List Nat := [32,152,94,107,6,143,11,57,124,120,221,43,52,199,247,8,146,60,200,35,122,97,242,90,76,176,222,9,64,51,17,116]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [27#u8,36#u8,178#u8,60#u8,73#u8,83#u8,57#u8,113#u8,193#u8,188#u8,24#u8,66#u8,54#u8,67#u8,142#u8,165#u8,173#u8,167#u8,105#u8,217#u8,189#u8,190#u8,96#u8,56#u8,201#u8,166#u8,112#u8,209#u8,81#u8,207#u8,34#u8,82#u8]
def n4 : List Nat := [27,36,178,60,73,83,57,113,193,188,24,66,54,67,142,165,173,167,105,217,189,190,96,56,201,166,112,209,81,207,34,82]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨13,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨13,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨13,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value13_0.selected JFn_Value13_1.selected JFn_Value13_2.selected JFn_Value13_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash003.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash003.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash003.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash003.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash003.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash003.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash003.message,JGc_TX2_M2.Hash003.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨13,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash003.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨13,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨13,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨13,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value003) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨13,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨13,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨13,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash003.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf13
end
