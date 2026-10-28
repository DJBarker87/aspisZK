import RPt_JFn_Value14_0
import RPt_JFn_Value14_1
import RPt_JFn_Value14_2
import RPt_JFn_Value14_3
import RPt_JFn_Value15_0
import RPt_JFn_Value15_1
import RPt_JFn_Value15_2
import RPt_JFn_Value15_3
import RPt_JFn_Value16_0
import RPt_JFn_Value16_1
import RPt_JFn_Value16_2
import RPt_JFn_Value16_3
import RPt_JFn_Value17_0
import RPt_JFn_Value17_1
import RPt_JFn_Value17_2
import RPt_JFn_Value17_3
import NDO_JGc_TX2_LeafHelpers
import NDO_JGc_TX2_M2Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf14
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value14_0.bytes
def n0 : List Nat := [11,175,81,16,21,114,186,105,233,129,133,15,160,130,42,47,234,205,138,78,203,55,232,62,52,149,202,47,225,179,160,113]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value14_1.bytes
def n1 : List Nat := [8,145,233,84,4,109,21,77,151,3,196,20,205,75,122,79,55,250,168,44,112,42,11,62,148,224,180,63,144,248,80,125]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value14_2.bytes
def n2 : List Nat := [9,113,218,102,233,173,99,95,41,180,243,116,102,163,222,84,115,115,211,112,251,202,46,15,128,10,44,77,58,156,74,5]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value14_3.bytes
def n3 : List Nat := [138,33,15,8,207,93,7,10,59,28,229,69,2,210,208,26,36,118,30,92,209,190,20,94,145,175,244,95,172,85,168,103]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [10#u8,218#u8,136#u8,28#u8,32#u8,143#u8,30#u8,219#u8,167#u8,185#u8,129#u8,32#u8,216#u8,177#u8,161#u8,224#u8,170#u8,154#u8,98#u8,170#u8,65#u8,250#u8,162#u8,51#u8,38#u8,66#u8,5#u8,216#u8,222#u8,45#u8,166#u8,30#u8]
def n4 : List Nat := [10,218,136,28,32,143,30,219,167,185,129,32,216,177,161,224,170,154,98,170,65,250,162,51,38,66,5,216,222,45,166,30]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨14,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨14,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨14,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value14_0.selected JFn_Value14_1.selected JFn_Value14_2.selected JFn_Value14_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash004.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash004.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash004.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash004.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash004.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash004.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash004.message,JGc_TX2_M2.Hash004.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨14,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash004.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨14,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨14,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨14,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value004) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨14,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨14,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨14,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash004.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf14
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf15
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value15_0.bytes
def n0 : List Nat := [2,96,73,104,221,236,229,76,46,196,58,13,68,58,193,34,157,10,17,27,231,46,207,1,76,45,191,113,41,242,230,103]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value15_1.bytes
def n1 : List Nat := [242,28,180,126,103,201,68,65,48,126,137,122,2,14,235,82,239,83,75,127,209,153,37,32,117,28,111,1,165,43,0,117]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value15_2.bytes
def n2 : List Nat := [229,36,87,31,229,62,222,22,180,174,114,122,154,90,65,58,49,219,227,127,132,221,146,119,206,167,40,62,211,40,124,44]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value15_3.bytes
def n3 : List Nat := [192,209,237,45,243,23,22,112,139,46,107,54,110,227,148,124,143,57,115,50,204,185,84,49,246,188,73,6,240,39,96,91]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [49#u8,29#u8,121#u8,136#u8,186#u8,102#u8,179#u8,162#u8,81#u8,121#u8,105#u8,148#u8,179#u8,121#u8,105#u8,235#u8,139#u8,83#u8,204#u8,233#u8,81#u8,192#u8,130#u8,241#u8,122#u8,123#u8,208#u8,71#u8,251#u8,106#u8,69#u8,9#u8]
def n4 : List Nat := [49,29,121,136,186,102,179,162,81,121,105,148,179,121,105,235,139,83,204,233,81,192,130,241,122,123,208,71,251,106,69,9]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨15,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨15,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨15,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value15_0.selected JFn_Value15_1.selected JFn_Value15_2.selected JFn_Value15_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash005.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash005.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash005.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash005.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash005.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash005.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash005.message,JGc_TX2_M2.Hash005.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨15,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash005.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨15,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨15,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨15,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value005) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨15,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨15,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨15,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash005.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf15
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf16
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value16_0.bytes
def n0 : List Nat := [45,148,20,98,103,235,242,73,42,245,251,38,141,180,101,52,133,91,84,102,236,30,96,45,81,95,43,31,74,8,39,104]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value16_1.bytes
def n1 : List Nat := [163,25,102,45,172,151,129,72,37,1,215,97,44,236,42,39,233,248,151,98,30,196,202,75,81,157,141,97,87,58,78,84]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value16_2.bytes
def n2 : List Nat := [30,146,220,25,14,74,162,47,146,194,193,75,56,180,151,12,166,151,39,26,255,5,71,82,215,191,168,53,111,41,87,17]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value16_3.bytes
def n3 : List Nat := [193,232,30,49,84,15,233,62,59,125,178,29,176,136,73,43,54,116,136,51,28,142,14,43,198,6,181,69,232,74,86,40]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [167#u8,214#u8,139#u8,248#u8,29#u8,101#u8,179#u8,124#u8,141#u8,169#u8,244#u8,57#u8,162#u8,196#u8,148#u8,83#u8,109#u8,217#u8,166#u8,96#u8,113#u8,153#u8,71#u8,32#u8,194#u8,182#u8,23#u8,176#u8,168#u8,247#u8,199#u8,12#u8]
def n4 : List Nat := [167,214,139,248,29,101,179,124,141,169,244,57,162,196,148,83,109,217,166,96,113,153,71,32,194,182,23,176,168,247,199,12]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨16,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof05.bytes,JFx_DataProof05.c00_length,JFx_DataProof05.c01_length,JFx_DataProof05.c02_length,JFx_DataProof05.c03_length,JFx_DataProof05.c04_length,JFx_DataProof05.c05_length,JFx_DataProof05.c06_length,JFx_DataProof05.c07_length,JFx_DataProof05.c08_length,JFx_DataProof05.c09_length,JFx_DataProof05.c10_length,JFx_DataProof05.c11_length,JFx_DataProof05.c12_length,JFx_DataProof05.c13_length,JFx_DataProof05.c14_length,JFx_DataProof05.c15_length,JFx_DataProof05.c16_length,JFx_DataProof05.c17_length,JFx_DataProof05.c18_length,JFx_DataProof05.c19_length,JFx_DataProof05.c20_length,JFx_DataProof05.c21_length,JFx_DataProof05.c22_length,JFx_DataProof05.c23_length,JFx_DataProof05.c24_length,JFx_DataProof05.c25_length,JFx_DataProof05.c26_length,JFx_DataProof05.c27_length,JFx_DataProof05.c28_length,JFx_DataProof05.c29_length,JFx_DataProof05.c30_length,JFx_DataProof05.c31_length,JFx_DataProof05.c32_length,JFx_DataProof05.c33_length,JFx_DataProof05.c34_length,JFx_DataProof05.c35_length,JFx_DataProof05.c36_length,JFx_DataProof05.c37_length,JFx_DataProof05.c38_length,JFx_DataProof05.c39_length,JFx_DataProof05.c40_length,JFx_DataProof05.c41_length,JFx_DataProof05.c42_length,JFx_DataProof05.c43_length,JFx_DataProof05.c44_length,JFx_DataProof05.c45_length,JFx_DataProof05.c46_length,JFx_DataProof05.c47_length,JFx_DataProof05.c48_length,JFx_DataProof05.c49_length,JFx_DataProof05.c50_length,JFx_DataProof05.c51_length,JFx_DataProof05.c52_length,JFx_DataProof05.c53_length,JFx_DataProof05.c54_length,JFx_DataProof05.c55_length,JFx_DataProof05.c56_length,JFx_DataProof05.c57_length,JFx_DataProof05.c58_length,JFx_DataProof05.c59_length,JFx_DataProof05.c60_length,JFx_DataProof05.c61_length,JFx_DataProof05.c62_length,JFx_DataProof05.c63_length,JFx_DataProof05.c64_length,JFx_DataProof05.c65_length,JFx_DataProof05.c66_length,JFx_DataProof05.c67_length,JFx_DataProof05.c68_length,JFx_DataProof05.c69_length,JFx_DataProof05.c70_length,JFx_DataProof05.c71_length,JFx_DataProof05.c72_length,JFx_DataProof05.c73_length,JFx_DataProof05.c74_length,JFx_DataProof05.c75_length,JFx_DataProof05.c76_length,JFx_DataProof05.c77_length,JFx_DataProof05.c78_length,JFx_DataProof05.c79_length,JFx_DataProof05.c80_length,JFx_DataProof05.c81_length,JFx_DataProof05.c82_length,JFx_DataProof05.c83_length,JFx_DataProof05.c84_length,JFx_DataProof05.c85_length,JFx_DataProof05.c86_length,JFx_DataProof05.c87_length,JFx_DataProof05.c88_length,JFx_DataProof05.c89_length,JFx_DataProof05.c90_length,JFx_DataProof05.c91_length,JFx_DataProof05.c92_length,JFx_DataProof05.c93_length,JFx_DataProof05.c94_length,JFx_DataProof05.c95_length,JFx_DataProof05.c96_length,JFx_DataProof05.c97_length,JFx_DataProof05.c98_length,JFx_DataProof05.c99_length,JFx_DataProof05.c100_length,JFx_DataProof05.c101_length,JFx_DataProof05.c102_length,JFx_DataProof05.c103_length,JFx_DataProof05.c104_length,JFx_DataProof05.c105_length,JFx_DataProof05.c106_length,JFx_DataProof05.c107_length,JFx_DataProof05.c108_length,JFx_DataProof05.c109_length,JFx_DataProof05.c110_length,JFx_DataProof05.c111_length,JFx_DataProof05.c112_length,JFx_DataProof05.c113_length,JFx_DataProof05.c114_length,JFx_DataProof05.c115_length,JFx_DataProof05.c116_length,JFx_DataProof05.c117_length,JFx_DataProof05.c118_length,JFx_DataProof05.c119_length,JFx_DataProof05.c120_length,JFx_DataProof05.c121_length,JFx_DataProof05.c122_length,JFx_DataProof05.c123_length,JFx_DataProof05.c124_length,JFx_DataProof05.c125_length,JFx_DataProof05.c126_length,JFx_DataProof05.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨16,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨16,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value16_0.selected JFn_Value16_1.selected JFn_Value16_2.selected JFn_Value16_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash006.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash006.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash006.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash006.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash006.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash006.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash006.message,JGc_TX2_M2.Hash006.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨16,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash006.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨16,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨16,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨16,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value006) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨16,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨16,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨16,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash006.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf16
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf17
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value17_0.bytes
def n0 : List Nat := [99,41,109,69,72,3,89,0,186,66,11,42,192,248,70,119,95,252,79,44,76,72,12,43,200,25,106,73,103,164,46,94]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value17_1.bytes
def n1 : List Nat := [204,56,90,42,52,170,234,36,205,137,181,70,96,173,206,47,38,28,88,17,18,96,9,91,60,252,98,106,116,153,246,104]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value17_2.bytes
def n2 : List Nat := [132,88,218,92,48,107,186,47,98,107,121,123,132,170,224,101,24,147,150,73,6,58,117,33,89,157,207,126,245,151,203,46]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value17_3.bytes
def n3 : List Nat := [80,167,238,72,15,68,98,16,199,211,208,104,152,65,213,44,21,95,186,94,78,140,75,105,254,172,214,80,220,135,183,15]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [111#u8,12#u8,46#u8,30#u8,234#u8,246#u8,85#u8,231#u8,102#u8,47#u8,45#u8,203#u8,7#u8,146#u8,248#u8,16#u8,81#u8,24#u8,58#u8,200#u8,50#u8,93#u8,159#u8,95#u8,223#u8,105#u8,102#u8,88#u8,2#u8,214#u8,119#u8,199#u8]
def n4 : List Nat := [111,12,46,30,234,246,85,231,102,47,45,203,7,146,248,16,81,24,58,200,50,93,159,95,223,105,102,88,2,214,119,199]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨17,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨17,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨17,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value17_0.selected JFn_Value17_1.selected JFn_Value17_2.selected JFn_Value17_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash007.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash007.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash007.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash007.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash007.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash007.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash007.message,JGc_TX2_M2.Hash007.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨17,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash007.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨17,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨17,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨17,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value007) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨17,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨17,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨17,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash007.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf17
end
