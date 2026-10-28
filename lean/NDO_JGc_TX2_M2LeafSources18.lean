import RPt_JFn_Value18_0
import RPt_JFn_Value18_1
import RPt_JFn_Value18_2
import RPt_JFn_Value18_3
import RPt_JFn_Value19_0
import RPt_JFn_Value19_1
import RPt_JFn_Value19_2
import RPt_JFn_Value19_3
import RPt_JFn_Value20_0
import RPt_JFn_Value20_1
import RPt_JFn_Value20_2
import RPt_JFn_Value20_3
import RPt_JFn_Value21_0
import RPt_JFn_Value21_1
import RPt_JFn_Value21_2
import RPt_JFn_Value21_3
import NDO_JGc_TX2_LeafHelpers
import NDO_JGc_TX2_M2Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf18
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value18_0.bytes
def n0 : List Nat := [62,56,176,79,220,118,161,77,203,37,240,40,125,150,193,3,39,11,101,117,18,32,81,63,91,97,4,62,238,152,132,49]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value18_1.bytes
def n1 : List Nat := [200,170,49,48,152,125,74,41,236,193,140,21,204,64,245,80,243,151,54,66,44,66,95,61,223,96,85,126,153,203,94,112]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value18_2.bytes
def n2 : List Nat := [42,219,145,66,214,77,49,8,85,128,225,67,33,86,105,123,99,246,85,92,146,229,34,95,217,147,45,8,127,248,151,16]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value18_3.bytes
def n3 : List Nat := [83,194,155,119,83,160,165,112,113,101,5,110,2,65,106,51,201,112,143,34,5,244,17,69,245,38,58,47,224,146,117,38]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [15#u8,184#u8,81#u8,16#u8,83#u8,27#u8,106#u8,124#u8,48#u8,41#u8,222#u8,45#u8,70#u8,141#u8,1#u8,187#u8,78#u8,119#u8,242#u8,239#u8,149#u8,82#u8,84#u8,51#u8,126#u8,112#u8,99#u8,110#u8,114#u8,89#u8,213#u8,0#u8]
def n4 : List Nat := [15,184,81,16,83,27,106,124,48,41,222,45,70,141,1,187,78,119,242,239,149,82,84,51,126,112,99,110,114,89,213,0]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨18,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨18,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨18,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value18_0.selected JFn_Value18_1.selected JFn_Value18_2.selected JFn_Value18_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash008.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash008.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash008.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash008.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash008.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash008.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash008.message,JGc_TX2_M2.Hash008.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨18,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash008.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨18,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨18,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨18,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value008) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨18,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨18,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨18,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash008.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf18
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf19
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value19_0.bytes
def n0 : List Nat := [90,129,159,17,216,188,2,29,114,251,224,64,113,216,128,77,176,182,162,37,131,35,103,2,157,230,197,75,190,253,183,19]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value19_1.bytes
def n1 : List Nat := [114,65,173,103,66,39,160,61,189,43,171,23,85,30,106,102,70,80,69,120,119,73,11,90,74,255,232,105,207,185,53,33]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value19_2.bytes
def n2 : List Nat := [168,141,159,104,237,178,98,3,186,180,213,57,64,201,10,111,255,138,220,37,7,25,104,43,60,76,249,37,51,107,35,50]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value19_3.bytes
def n3 : List Nat := [128,188,7,87,22,120,156,10,94,83,87,73,165,89,45,95,162,235,226,43,26,97,208,119,10,7,54,60,230,106,145,110]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [14#u8,138#u8,135#u8,108#u8,49#u8,244#u8,100#u8,195#u8,150#u8,56#u8,24#u8,160#u8,232#u8,133#u8,23#u8,222#u8,213#u8,231#u8,107#u8,38#u8,160#u8,154#u8,80#u8,149#u8,119#u8,64#u8,19#u8,109#u8,71#u8,3#u8,211#u8,176#u8]
def n4 : List Nat := [14,138,135,108,49,244,100,195,150,56,24,160,232,133,23,222,213,231,107,38,160,154,80,149,119,64,19,109,71,3,211,176]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨19,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨19,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨19,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value19_0.selected JFn_Value19_1.selected JFn_Value19_2.selected JFn_Value19_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash009.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash009.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash009.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash009.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash009.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash009.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash009.message,JGc_TX2_M2.Hash009.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨19,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash009.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨19,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨19,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨19,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value009) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨19,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨19,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨19,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash009.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf19
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf20
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value20_0.bytes
def n0 : List Nat := [158,151,196,46,221,59,81,17,234,151,12,114,133,2,83,76,115,6,212,71,174,225,4,125,58,231,127,79,131,97,217,112]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value20_1.bytes
def n1 : List Nat := [86,134,121,93,32,229,128,100,229,161,180,66,125,43,135,87,79,126,52,107,211,88,158,7,124,75,30,80,19,36,213,57]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value20_2.bytes
def n2 : List Nat := [240,160,142,49,115,130,252,73,233,220,57,105,9,14,192,13,144,190,173,116,242,247,7,22,0,182,104,10,140,254,201,99]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value20_3.bytes
def n3 : List Nat := [210,66,199,82,4,40,94,25,28,178,119,55,144,87,111,76,39,199,47,92,45,150,216,59,217,127,125,14,188,107,55,8]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [55#u8,93#u8,198#u8,15#u8,230#u8,137#u8,196#u8,115#u8,123#u8,230#u8,212#u8,155#u8,106#u8,211#u8,223#u8,109#u8,249#u8,1#u8,50#u8,31#u8,220#u8,103#u8,114#u8,91#u8,190#u8,6#u8,233#u8,219#u8,106#u8,125#u8,176#u8,234#u8]
def n4 : List Nat := [55,93,198,15,230,137,196,115,123,230,212,155,106,211,223,109,249,1,50,31,220,103,114,91,190,6,233,219,106,125,176,234]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨20,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨20,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨20,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value20_0.selected JFn_Value20_1.selected JFn_Value20_2.selected JFn_Value20_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash010.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash010.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash010.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash010.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash010.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash010.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash010.message,JGc_TX2_M2.Hash010.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨20,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash010.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨20,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨20,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨20,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value010) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨20,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨20,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨20,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash010.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf20
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Leaf21
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
def c0 : List U8 := JFn_Value21_0.bytes
def n0 : List Nat := [3,223,66,89,120,244,219,39,202,100,2,31,193,70,131,112,30,209,118,64,152,62,127,122,232,217,198,64,66,87,21,21]
theorem cast0 : (c0.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n0 := by rfl
#print axioms cast0
def c1 : List U8 := JFn_Value21_1.bytes
def n1 : List Nat := [35,172,30,84,70,166,77,67,154,224,84,105,188,247,140,76,172,101,146,29,179,52,218,117,188,248,19,98,215,43,54,108]
theorem cast1 : (c1.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n1 := by rfl
#print axioms cast1
def c2 : List U8 := JFn_Value21_2.bytes
def n2 : List Nat := [78,135,85,26,198,234,42,98,222,212,71,94,191,158,193,85,142,26,127,8,12,13,234,109,66,169,180,124,184,172,174,73]
theorem cast2 : (c2.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n2 := by rfl
#print axioms cast2
def c3 : List U8 := JFn_Value21_3.bytes
def n3 : List Nat := [5,210,64,37,247,95,27,22,137,17,20,36,157,177,72,69,224,114,124,63,122,190,201,30,111,41,111,69,184,145,27,61]
theorem cast3 : (c3.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n3 := by rfl
#print axioms cast3
def c4 : List U8 := [247#u8,229#u8,197#u8,123#u8,149#u8,116#u8,219#u8,84#u8,39#u8,33#u8,54#u8,204#u8,180#u8,77#u8,193#u8,112#u8,104#u8,166#u8,3#u8,36#u8,35#u8,230#u8,189#u8,2#u8,38#u8,160#u8,249#u8,22#u8,217#u8,91#u8,113#u8,234#u8]
def n4 : List Nat := [247,229,197,123,149,116,219,84,39,33,54,204,180,77,193,112,104,166,3,36,35,230,189,2,38,160,249,22,217,91,113,234]
theorem cast4 : (c4.map AspisV8R19.SqueezeOracleBridge.decodeByte).map Fin.val=n4 := by rfl
#print axioms cast4
theorem salt : ((JFo_Opening.value ⟨21,by decide⟩).val.drop 800).take 32=c4 := by
  rw [JFo_Opening.selected,JFq_Range.nested _ _ 832 800 32 (by decide)]
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof06.bytes,JFx_DataProof06.c00_length,JFx_DataProof06.c01_length,JFx_DataProof06.c02_length,JFx_DataProof06.c03_length,JFx_DataProof06.c04_length,JFx_DataProof06.c05_length,JFx_DataProof06.c06_length,JFx_DataProof06.c07_length,JFx_DataProof06.c08_length,JFx_DataProof06.c09_length,JFx_DataProof06.c10_length,JFx_DataProof06.c11_length,JFx_DataProof06.c12_length,JFx_DataProof06.c13_length,JFx_DataProof06.c14_length,JFx_DataProof06.c15_length,JFx_DataProof06.c16_length,JFx_DataProof06.c17_length,JFx_DataProof06.c18_length,JFx_DataProof06.c19_length,JFx_DataProof06.c20_length,JFx_DataProof06.c21_length,JFx_DataProof06.c22_length,JFx_DataProof06.c23_length,JFx_DataProof06.c24_length,JFx_DataProof06.c25_length,JFx_DataProof06.c26_length,JFx_DataProof06.c27_length,JFx_DataProof06.c28_length,JFx_DataProof06.c29_length,JFx_DataProof06.c30_length,JFx_DataProof06.c31_length,JFx_DataProof06.c32_length,JFx_DataProof06.c33_length,JFx_DataProof06.c34_length,JFx_DataProof06.c35_length,JFx_DataProof06.c36_length,JFx_DataProof06.c37_length,JFx_DataProof06.c38_length,JFx_DataProof06.c39_length,JFx_DataProof06.c40_length,JFx_DataProof06.c41_length,JFx_DataProof06.c42_length,JFx_DataProof06.c43_length,JFx_DataProof06.c44_length,JFx_DataProof06.c45_length,JFx_DataProof06.c46_length,JFx_DataProof06.c47_length,JFx_DataProof06.c48_length,JFx_DataProof06.c49_length,JFx_DataProof06.c50_length,JFx_DataProof06.c51_length,JFx_DataProof06.c52_length,JFx_DataProof06.c53_length,JFx_DataProof06.c54_length,JFx_DataProof06.c55_length,JFx_DataProof06.c56_length,JFx_DataProof06.c57_length,JFx_DataProof06.c58_length,JFx_DataProof06.c59_length,JFx_DataProof06.c60_length,JFx_DataProof06.c61_length,JFx_DataProof06.c62_length,JFx_DataProof06.c63_length,JFx_DataProof06.c64_length,JFx_DataProof06.c65_length,JFx_DataProof06.c66_length,JFx_DataProof06.c67_length,JFx_DataProof06.c68_length,JFx_DataProof06.c69_length,JFx_DataProof06.c70_length,JFx_DataProof06.c71_length,JFx_DataProof06.c72_length,JFx_DataProof06.c73_length,JFx_DataProof06.c74_length,JFx_DataProof06.c75_length,JFx_DataProof06.c76_length,JFx_DataProof06.c77_length,JFx_DataProof06.c78_length,JFx_DataProof06.c79_length,JFx_DataProof06.c80_length,JFx_DataProof06.c81_length,JFx_DataProof06.c82_length,JFx_DataProof06.c83_length,JFx_DataProof06.c84_length,JFx_DataProof06.c85_length,JFx_DataProof06.c86_length,JFx_DataProof06.c87_length,JFx_DataProof06.c88_length,JFx_DataProof06.c89_length,JFx_DataProof06.c90_length,JFx_DataProof06.c91_length,JFx_DataProof06.c92_length,JFx_DataProof06.c93_length,JFx_DataProof06.c94_length,JFx_DataProof06.c95_length,JFx_DataProof06.c96_length,JFx_DataProof06.c97_length,JFx_DataProof06.c98_length,JFx_DataProof06.c99_length,JFx_DataProof06.c100_length,JFx_DataProof06.c101_length,JFx_DataProof06.c102_length,JFx_DataProof06.c103_length,JFx_DataProof06.c104_length,JFx_DataProof06.c105_length,JFx_DataProof06.c106_length,JFx_DataProof06.c107_length,JFx_DataProof06.c108_length,JFx_DataProof06.c109_length,JFx_DataProof06.c110_length,JFx_DataProof06.c111_length,JFx_DataProof06.c112_length,JFx_DataProof06.c113_length,JFx_DataProof06.c114_length,JFx_DataProof06.c115_length,JFx_DataProof06.c116_length,JFx_DataProof06.c117_length,JFx_DataProof06.c118_length,JFx_DataProof06.c119_length,JFx_DataProof06.c120_length,JFx_DataProof06.c121_length,JFx_DataProof06.c122_length,JFx_DataProof06.c123_length,JFx_DataProof06.c124_length,JFx_DataProof06.c125_length,JFx_DataProof06.c126_length,JFx_DataProof06.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms salt
theorem values : ((JFo_Opening.value ⟨21,by decide⟩).val.drop 672).take 128=c0++c1++c2++c3 := by
  change (JFn_ValueBlock.value ⟨21,by decide⟩).val=c0++c1++c2++c3
  exact JGc_TX2_LeafHelpers.four _ c0 c1 c2 c3 (JFn_ValueBlock.length _)
    JFn_Value21_0.selected JFn_Value21_1.selected JFn_Value21_2.selected JFn_Value21_3.selected
#print axioms values
def numeric : List Nat := [16,114]++n0++n1++n2++n3++n4
def rest1 : List Nat := n1.drop 30++n2++n3++n4
def rest2 : List Nat := n3.drop 30++n4
theorem regroup : numeric=JGc_TX2_M2.Hash011.message := by
  have step0 : [16,114]++n0++n1=JGc_TX2_M2.Hash011.B00.input++n1.drop 30 := by rfl
  have step1 : n1.drop 30++n2++n3=JGc_TX2_M2.Hash011.B01.input++n3.drop 30 := by rfl
  have step2 : rest2=JGc_TX2_M2.Hash011.tail := by rfl
  have h0 : numeric=JGc_TX2_M2.Hash011.B00.input++rest1 := by
    simpa only [numeric,rest1,List.append_assoc] using congrArg (fun xs : List Nat => xs++n2++n3++n4) step0
  have h1 : rest1=JGc_TX2_M2.Hash011.B01.input++rest2 := by
    simpa only [rest1,rest2,List.append_assoc] using congrArg (fun xs : List Nat => xs++n4) step1
  rw [h0,h1,step2]
  simp only [JGc_TX2_M2.Hash011.message,JGc_TX2_M2.Hash011.head,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc]
#print axioms regroup

theorem address : (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨21,by decide⟩))).map Fin.val=JGc_TX2_M2.Hash011.message := by
  rw [Port4B_LeafCode.input,if_neg (by decide : ¬2#usize=0#usize),if_neg (by decide : ¬2#usize=1#usize)]
  simp only [Port4B_LeafCode.parts,flatten,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  have hv : (MultiproofConeSlices.sub (JFo_Opening.value ⟨21,by decide⟩) 672#usize 800#usize).val=c0++c1++c2++c3 := values
  have hs : (MultiproofConeSlices.sub (JFo_Opening.value ⟨21,by decide⟩) 800#usize 832#usize).val=c4 := salt
  rw [hv,hs]
  simp only [List.map_append,List.map_cons,List.map_nil,cast0,cast1,cast2,cast3,cast4]
  have h16 : (16#u8).val=16 := by scalar_tac
  have h114 : (114#u8).val=114 := by scalar_tac
  simpa only [numeric,List.append_assoc,AspisV8R19.SqueezeOracleBridge.decodeByte,h16,h114] using regroup
#print axioms address

theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    Port4B_LeafCode.native {D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts}
      hash 2#usize (JFo_Opening.value ⟨21,by decide⟩)=ok (encodeState JGc_TX2_M2Roots.value011) := by
  rw [show Port4B_LeafCode.native _ hash 2#usize (JFo_Opening.value ⟨21,by decide⟩)=
    ({D with digest := fun _ parts => F3U_Oracle.hashv JFp_SHADigest.digest parts} : AspisR1Stage2.aspis_core.digest.Digest32 Hash).digest hash
      (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨21,by decide⟩)) from
        (Port4B_LeafCode.code_exact _ hash _ _ (JFo_Opening.length _) []).1]
  change ok (encodeState (JFp_SHADigest.digest (flatten (Port4B_LeafCode.input 2#usize (JFo_Opening.value ⟨21,by decide⟩)))))=_
  unfold JFp_SHADigest.digest
  rw [address,JGc_TX2_M2.Hash011.checked]
  rfl
#print axioms source
end AspisR1.JGc_TX2_M2Leaf21
end
