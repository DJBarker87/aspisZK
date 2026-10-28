import NDO_JHn_R_JHh_C_Tree2B_L1
import RPt_JFq_Range
import NDO_JFw_Frames
import NDO_JGm_TX2_View
import NDO_JGp_Opening0
import NDO_JGp_Opening1
import NDO_JGp_Opening2
import NDO_JGp_Opening3
import NDO_JGp_Opening4
import NDO_JGp_Opening5
import NDO_JGp_Opening6
import NDO_JGp_Opening7
import NDO_JGp_Opening8
import NDO_JGp_Opening9
import NDO_JGu_Keys
import NDO_JGy_LightCore
import NDO_JGy_LightPadding
import NDO_JHn_R_JHh_C_Tree2A
import NDO_JHe_SHARealization
import Port4B_KeyDecode
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_00
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
def values00 : List (Array U8 32#usize) := [encodeState value006,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 16398#u32 0#usize (encodeState value010) 32#usize
 def indices01 : List U32 := [8199#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value010,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 23374#u32 1#usize (encodeState value011) 64#usize
 def indices02 : List U32 := [8199#u32,11687#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 36882#u32 2#usize (encodeState value012) 96#usize
 def indices03 : List U32 := [8199#u32,11687#u32,18441#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 39953#u32 3#usize (encodeState value013) 128#usize
 def indices04 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 45964#u32 4#usize (encodeState value014) 160#usize
 def indices05 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 48079#u32 5#usize (encodeState value015) 192#usize
 def indices06 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 48273#u32 6#usize (encodeState value016) 224#usize
 def indices07 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,52342#u32,54205#u32,61474#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value004,encodeState value002,encodeState value003]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 52342#u32 7#usize (encodeState value017) 256#usize
 def indices08 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,54205#u32,61474#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value002,encodeState value003]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 54205#u32 8#usize (encodeState value018) 288#usize
 def indices09 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,61474#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value003]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 61474#u32 9#usize (encodeState value019) 320#usize
 def indices10 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      0#usize 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 0#usize 32#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 0#usize 32#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 0).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37703).take 32)=(encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 0#usize 32#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      32#usize 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 32#usize 64#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 32#usize 64#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 32).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37735).take 32)=(encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 32#usize 64#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      64#usize 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 64#usize 96#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 64#usize 96#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 64).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37767).take 32)=(encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 64#usize 96#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      96#usize 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 96#usize 128#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 96#usize 128#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 96).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37799).take 32)=(encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 96#usize 128#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      128#usize 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 128#usize 160#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 128#usize 160#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 128).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37831).take 32)=(encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 128#usize 160#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      160#usize 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 160#usize 192#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 160#usize 192#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 160).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37863).take 32)=(encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 160#usize 192#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      192#usize 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 192#usize 224#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 192#usize 224#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 192).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37895).take 32)=(encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 192#usize 224#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      224#usize 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 224#usize 256#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 224#usize 256#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 224).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37927).take 32)=(encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 224#usize 256#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      256#usize 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 256#usize 288#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 256#usize 288#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 256).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37959).take 32)=(encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 256#usize 288#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      288#usize 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 288#usize 320#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 288#usize 320#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 288).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 37991).take 32)=(encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 288#usize 320#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 0) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 320 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 0 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 16398#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value006) :=
    JGm_TX2_View.value (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=0#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠16398#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨23374#u32,JGm_TX2_View.index (s00 s) indices00 values00 0 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 32#usize 3840#usize
    16398#u32 (encodeState value006) (encodeState (JGc_TX2_HashBytes.state [59,19,2,0,169,92,95,200,80,218,215,254,63,229,202,59,255,62,34,152,178,252,191,0,154,18,160,100,127,195,236,140])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 16398#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source010 D hash (s00 s) 1#usize 32#usize 16398#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 32 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 0 v00
      16398#u32 0#usize (encodeState value010) 32#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 23374#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value000) :=
    JGm_TX2_View.value (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=32#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠23374#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36882#u32,JGm_TX2_View.index (s01 s) indices01 values01 32 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 64#usize 3808#usize
    23374#u32 (encodeState value000) (encodeState (JGc_TX2_HashBytes.state [157,250,64,85,13,19,77,148,29,212,154,20,167,121,250,170,228,41,109,0,8,18,69,253,189,146,93,22,157,14,22,87])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 23374#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source011 D hash (s01 s) 2#usize 64#usize 23374#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 64 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 32 v01
      23374#u32 1#usize (encodeState value011) 64#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 36882#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value001) :=
    JGm_TX2_View.value (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=64#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠36882#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨39953#u32,JGm_TX2_View.index (s02 s) indices02 values02 64 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 96#usize 3776#usize
    36882#u32 (encodeState value001) (encodeState (JGc_TX2_HashBytes.state [200,118,125,216,76,197,168,252,66,166,175,172,159,132,202,150,238,183,109,182,215,230,204,48,38,187,56,127,4,148,156,91])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 36882#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source012 D hash (s02 s) 3#usize 96#usize 36882#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 96 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 64 v02
      36882#u32 2#usize (encodeState value012) 96#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 39953#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value009) :=
    JGm_TX2_View.value (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=96#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠39953#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨45964#u32,JGm_TX2_View.index (s03 s) indices03 values03 96 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 128#usize 3744#usize
    39953#u32 (encodeState value009) (encodeState (JGc_TX2_HashBytes.state [212,242,126,73,163,36,230,105,69,72,183,184,38,238,26,19,12,17,111,26,165,123,45,242,32,167,200,96,233,228,57,69])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 39953#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source013 D hash (s03 s) 4#usize 128#usize 39953#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 128 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 96 v03
      39953#u32 3#usize (encodeState value013) 128#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 45964#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value007) :=
    JGm_TX2_View.value (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=128#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠45964#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨48079#u32,JGm_TX2_View.index (s04 s) indices04 values04 128 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 160#usize 3712#usize
    45964#u32 (encodeState value007) (encodeState (JGc_TX2_HashBytes.state [82,191,91,24,205,192,231,67,121,98,110,223,12,88,203,10,225,19,214,220,215,156,248,27,81,185,96,114,168,9,78,14])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 45964#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source014 D hash (s04 s) 5#usize 160#usize 45964#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 160 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 128 v04
      45964#u32 4#usize (encodeState value014) 160#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 48079#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value005) :=
    JGm_TX2_View.value (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=160#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠48079#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨48273#u32,JGm_TX2_View.index (s05 s) indices05 values05 160 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 192#usize 3680#usize
    48079#u32 (encodeState value005) (encodeState (JGc_TX2_HashBytes.state [133,193,193,242,18,135,93,234,189,30,36,64,27,220,184,7,144,101,221,10,71,70,1,222,233,39,21,21,157,144,185,165])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 48079#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source015 D hash (s05 s) 6#usize 192#usize 48079#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 192 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 160 v05
      48079#u32 5#usize (encodeState value015) 192#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 48273#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value008) :=
    JGm_TX2_View.value (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=192#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠48273#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨52342#u32,JGm_TX2_View.index (s06 s) indices06 values06 192 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 224#usize 3648#usize
    48273#u32 (encodeState value008) (encodeState (JGc_TX2_HashBytes.state [98,207,122,12,13,116,247,26,12,101,199,43,169,75,183,42,84,151,241,175,190,14,219,79,255,20,41,230,147,83,213,218])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 48273#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source016 D hash (s06 s) 7#usize 224#usize 48273#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 224 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 192 v06
      48273#u32 6#usize (encodeState value016) 224#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 52342#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value004) :=
    JGm_TX2_View.value (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=224#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠52342#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨54205#u32,JGm_TX2_View.index (s07 s) indices07 values07 224 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 256#usize 3616#usize
    52342#u32 (encodeState value004) (encodeState (JGc_TX2_HashBytes.state [80,151,219,68,228,150,38,180,212,171,144,75,12,109,31,147,55,20,109,143,198,101,8,244,28,178,249,159,227,18,96,225])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 52342#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source017 D hash (s07 s) 8#usize 256#usize 52342#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 256 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 224 v07
      52342#u32 7#usize (encodeState value017) 256#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 54205#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value002) :=
    JGm_TX2_View.value (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=256#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠54205#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨61474#u32,JGm_TX2_View.index (s08 s) indices08 values08 256 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 288#usize 3584#usize
    54205#u32 (encodeState value002) (encodeState (JGc_TX2_HashBytes.state [52,8,95,13,105,245,56,139,100,239,201,233,12,0,102,84,64,208,206,160,240,46,2,104,110,111,39,205,28,111,190,253])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 54205#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source018 D hash (s08 s) 9#usize 288#usize 54205#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 288 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 256 v08
      54205#u32 8#usize (encodeState value018) 288#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 61474#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value003) :=
    JGm_TX2_View.value (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=288#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠61474#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 320#usize 3552#usize
    61474#u32 (encodeState value003) (encodeState (JGc_TX2_HashBytes.state [58,245,80,88,37,211,128,187,23,227,240,163,220,232,101,152,153,152,109,88,252,196,25,246,154,119,211,100,33,86,172,156])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 61474#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source019 D hash (s09 s) 10#usize 320#usize 61474#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 320 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 288 v09
      61474#u32 9#usize (encodeState value019) 320#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 320
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_00
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_01
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
def values00 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 8199#u32 0#usize (encodeState value020) 352#usize
 def indices01 : List U32 := [4099#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value020,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 11687#u32 1#usize (encodeState value021) 384#usize
 def indices02 : List U32 := [4099#u32,5843#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 18441#u32 2#usize (encodeState value022) 416#usize
 def indices03 : List U32 := [4099#u32,5843#u32,9220#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 19976#u32 3#usize (encodeState value023) 448#usize
 def indices04 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 22982#u32 4#usize (encodeState value024) 480#usize
 def indices05 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 24039#u32 5#usize (encodeState value025) 512#usize
 def indices06 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 24136#u32 6#usize (encodeState value026) 544#usize
 def indices07 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,26171#u32,27102#u32,30737#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value017,encodeState value018,encodeState value019]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 26171#u32 7#usize (encodeState value027) 576#usize
 def indices08 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,27102#u32,30737#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value018,encodeState value019]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 27102#u32 8#usize (encodeState value028) 608#usize
 def indices09 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,30737#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value019]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 30737#u32 9#usize (encodeState value029) 640#usize
 def indices10 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      320#usize 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 320#usize 352#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 320#usize 352#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 320).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38023).take 32)=(encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 320#usize 352#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      352#usize 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 352#usize 384#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 352#usize 384#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 352).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38055).take 32)=(encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 352#usize 384#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      384#usize 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 384#usize 416#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 384#usize 416#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 384).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38087).take 32)=(encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 384#usize 416#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      416#usize 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 416#usize 448#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 416#usize 448#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 416).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38119).take 32)=(encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 416#usize 448#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      448#usize 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 448#usize 480#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 448#usize 480#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 448).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38151).take 32)=(encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 448#usize 480#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      480#usize 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 480#usize 512#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 480#usize 512#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 480).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38183).take 32)=(encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 480#usize 512#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      512#usize 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 512#usize 544#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 512#usize 544#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 512).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38215).take 32)=(encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 512#usize 544#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      544#usize 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 544#usize 576#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 544#usize 576#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 544).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38247).take 32)=(encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 544#usize 576#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      576#usize 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 576#usize 608#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 576#usize 608#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 576).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38279).take 32)=(encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 576#usize 608#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      608#usize 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 608#usize 640#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 608#usize 640#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 608).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38311).take 32)=(encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 608#usize 640#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 320) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 640 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 320 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 8199#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value010) :=
    JGm_TX2_View.value (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=320#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠8199#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11687#u32,JGm_TX2_View.index (s00 s) indices00 values00 320 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 352#usize 3520#usize
    8199#u32 (encodeState value010) (encodeState (JGc_TX2_HashBytes.state [179,57,66,105,91,88,148,117,98,202,23,143,65,232,228,202,11,120,180,169,158,103,229,95,32,200,194,222,112,210,131,3])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 8199#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source020 D hash (s00 s) 1#usize 352#usize 8199#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 352 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 320 v00
      8199#u32 0#usize (encodeState value020) 352#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 11687#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value011) :=
    JGm_TX2_View.value (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=352#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠11687#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨18441#u32,JGm_TX2_View.index (s01 s) indices01 values01 352 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 384#usize 3488#usize
    11687#u32 (encodeState value011) (encodeState (JGc_TX2_HashBytes.state [107,125,164,219,26,17,227,219,9,238,70,117,237,24,14,190,244,82,156,147,101,254,180,116,45,28,98,62,32,57,198,231])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 11687#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source021 D hash (s01 s) 2#usize 384#usize 11687#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 384 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 352 v01
      11687#u32 1#usize (encodeState value021) 384#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 18441#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value012) :=
    JGm_TX2_View.value (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=384#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠18441#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨19976#u32,JGm_TX2_View.index (s02 s) indices02 values02 384 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 416#usize 3456#usize
    18441#u32 (encodeState value012) (encodeState (JGc_TX2_HashBytes.state [47,141,216,252,197,166,70,210,81,178,177,38,252,245,63,138,90,15,229,137,148,184,253,55,25,241,20,143,57,249,114,136])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 18441#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source022 D hash (s02 s) 3#usize 416#usize 18441#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 416 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 384 v02
      18441#u32 2#usize (encodeState value022) 416#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 19976#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value013) :=
    JGm_TX2_View.value (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=416#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠19976#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨22982#u32,JGm_TX2_View.index (s03 s) indices03 values03 416 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 448#usize 3424#usize
    19976#u32 (encodeState value013) (encodeState (JGc_TX2_HashBytes.state [149,82,100,53,22,189,226,92,234,12,68,130,93,161,194,244,133,5,197,140,65,188,52,164,91,170,182,75,33,104,183,190])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 19976#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source023 D hash (s03 s) 4#usize 448#usize 19976#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 448 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 416 v03
      19976#u32 3#usize (encodeState value023) 448#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 22982#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value014) :=
    JGm_TX2_View.value (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=448#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠22982#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨24039#u32,JGm_TX2_View.index (s04 s) indices04 values04 448 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 480#usize 3392#usize
    22982#u32 (encodeState value014) (encodeState (JGc_TX2_HashBytes.state [153,116,202,141,139,28,14,167,146,44,161,154,154,150,133,164,1,97,251,129,67,238,209,205,47,38,121,56,63,172,240,59])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 22982#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source024 D hash (s04 s) 5#usize 480#usize 22982#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 480 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 448 v04
      22982#u32 4#usize (encodeState value024) 480#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 24039#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value015) :=
    JGm_TX2_View.value (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=480#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠24039#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨24136#u32,JGm_TX2_View.index (s05 s) indices05 values05 480 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 512#usize 3360#usize
    24039#u32 (encodeState value015) (encodeState (JGc_TX2_HashBytes.state [59,32,195,3,19,154,209,61,43,191,156,113,54,238,181,159,13,241,5,114,216,99,9,206,156,21,132,19,133,169,28,149])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 24039#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source025 D hash (s05 s) 6#usize 512#usize 24039#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 512 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 480 v05
      24039#u32 5#usize (encodeState value025) 512#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 24136#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value016) :=
    JGm_TX2_View.value (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=512#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠24136#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨26171#u32,JGm_TX2_View.index (s06 s) indices06 values06 512 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 544#usize 3328#usize
    24136#u32 (encodeState value016) (encodeState (JGc_TX2_HashBytes.state [160,150,74,176,230,87,55,149,137,239,129,40,128,128,155,164,228,20,84,10,90,170,136,112,178,54,174,236,18,211,106,20])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 24136#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source026 D hash (s06 s) 7#usize 544#usize 24136#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 544 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 512 v06
      24136#u32 6#usize (encodeState value026) 544#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 26171#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value017) :=
    JGm_TX2_View.value (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=544#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠26171#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨27102#u32,JGm_TX2_View.index (s07 s) indices07 values07 544 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 576#usize 3296#usize
    26171#u32 (encodeState value017) (encodeState (JGc_TX2_HashBytes.state [228,12,216,182,13,245,17,244,56,172,67,209,165,228,216,245,36,207,219,252,76,56,80,233,32,172,129,152,94,206,186,32])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 26171#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source027 D hash (s07 s) 8#usize 576#usize 26171#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 576 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 544 v07
      26171#u32 7#usize (encodeState value027) 576#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 27102#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value018) :=
    JGm_TX2_View.value (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=576#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠27102#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨30737#u32,JGm_TX2_View.index (s08 s) indices08 values08 576 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 608#usize 3264#usize
    27102#u32 (encodeState value018) (encodeState (JGc_TX2_HashBytes.state [188,221,111,216,18,217,30,136,2,223,90,61,66,1,162,238,11,64,13,125,84,37,35,58,104,178,136,54,100,76,168,41])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 27102#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source028 D hash (s08 s) 9#usize 608#usize 27102#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 608 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 576 v08
      27102#u32 8#usize (encodeState value028) 608#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 30737#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value019) :=
    JGm_TX2_View.value (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=608#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠30737#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 640#usize 3232#usize
    30737#u32 (encodeState value019) (encodeState (JGc_TX2_HashBytes.state [41,72,84,86,132,77,231,158,173,214,235,170,124,62,85,192,227,36,17,210,21,206,189,190,89,89,69,162,196,143,89,105])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 30737#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source029 D hash (s09 s) 10#usize 640#usize 30737#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 640 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 608 v09
      30737#u32 9#usize (encodeState value029) 640#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 640
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_01
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level2_02
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M2Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes2
def indices00 : List U32 := [4099#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
def values00 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 4099#u32 0#usize (encodeState value030) 672#usize
 def indices01 : List U32 := [2049#u32,5843#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value030,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 5843#u32 1#usize (encodeState value031) 704#usize
 def indices02 : List U32 := [2049#u32,2921#u32,9220#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 9220#u32 2#usize (encodeState value032) 736#usize
 def indices03 : List U32 := [2049#u32,2921#u32,4610#u32,9988#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 9988#u32 3#usize (encodeState value033) 768#usize
 def indices04 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,11491#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 11491#u32 4#usize (encodeState value034) 800#usize
 def indices05 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,12019#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 12019#u32 5#usize (encodeState value035) 832#usize
 def indices06 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,12068#u32,13085#u32,13551#u32,15368#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 12068#u32 6#usize (encodeState value036) 864#usize
 def indices07 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,13085#u32,13551#u32,15368#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value027,encodeState value028,encodeState value029]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 13085#u32 7#usize (encodeState value037) 896#usize
 def indices08 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,13551#u32,15368#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value028,encodeState value029]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 13551#u32 8#usize (encodeState value038) 928#usize
 def indices09 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,15368#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value029]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 15368#u32 9#usize (encodeState value039) 960#usize
 def indices10 : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [2049#u32,2921#u32,4610#u32,4994#u32,5745#u32,6009#u32,6034#u32,6542#u32,6775#u32,7684#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      640#usize 672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 640#usize 672#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 640#usize 672#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 640).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38343).take 32)=(encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 640#usize 672#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      672#usize 704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 672#usize 704#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 672#usize 704#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 672).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38375).take 32)=(encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 672#usize 704#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      704#usize 736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 704#usize 736#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 704#usize 736#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 704).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38407).take 32)=(encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 704#usize 736#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      736#usize 768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 736#usize 768#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 736#usize 768#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 736).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38439).take 32)=(encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 736#usize 768#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      768#usize 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 768#usize 800#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 768#usize 800#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 768).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38471).take 32)=(encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 768#usize 800#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      800#usize 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 800#usize 832#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 800#usize 832#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 800).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38503).take 32)=(encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 800#usize 832#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      832#usize 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 832#usize 864#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 832#usize 864#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 832).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38535).take 32)=(encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 832#usize 864#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      864#usize 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 864#usize 896#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 864#usize 896#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 864).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38567).take 32)=(encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 864#usize 896#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      896#usize 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 896#usize 928#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 896#usize 928#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 896).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38599).take 32)=(encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 896#usize 928#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      928#usize 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])) := by
  unfold JGy_G_JGu_Supplied.nodes2
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot2.value 3840#usize 928#usize 960#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot2.value 928#usize 960#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])).val := by
    change (((JFw_Frames.window 37703 4096).val.drop 928).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 38631).take 32)=(encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof09.bytes,JFx_DataProof09.c00_length,JFx_DataProof09.c01_length,JFx_DataProof09.c02_length,JFx_DataProof09.c03_length,JFx_DataProof09.c04_length,JFx_DataProof09.c05_length,JFx_DataProof09.c06_length,JFx_DataProof09.c07_length,JFx_DataProof09.c08_length,JFx_DataProof09.c09_length,JFx_DataProof09.c10_length,JFx_DataProof09.c11_length,JFx_DataProof09.c12_length,JFx_DataProof09.c13_length,JFx_DataProof09.c14_length,JFx_DataProof09.c15_length,JFx_DataProof09.c16_length,JFx_DataProof09.c17_length,JFx_DataProof09.c18_length,JFx_DataProof09.c19_length,JFx_DataProof09.c20_length,JFx_DataProof09.c21_length,JFx_DataProof09.c22_length,JFx_DataProof09.c23_length,JFx_DataProof09.c24_length,JFx_DataProof09.c25_length,JFx_DataProof09.c26_length,JFx_DataProof09.c27_length,JFx_DataProof09.c28_length,JFx_DataProof09.c29_length,JFx_DataProof09.c30_length,JFx_DataProof09.c31_length,JFx_DataProof09.c32_length,JFx_DataProof09.c33_length,JFx_DataProof09.c34_length,JFx_DataProof09.c35_length,JFx_DataProof09.c36_length,JFx_DataProof09.c37_length,JFx_DataProof09.c38_length,JFx_DataProof09.c39_length,JFx_DataProof09.c40_length,JFx_DataProof09.c41_length,JFx_DataProof09.c42_length,JFx_DataProof09.c43_length,JFx_DataProof09.c44_length,JFx_DataProof09.c45_length,JFx_DataProof09.c46_length,JFx_DataProof09.c47_length,JFx_DataProof09.c48_length,JFx_DataProof09.c49_length,JFx_DataProof09.c50_length,JFx_DataProof09.c51_length,JFx_DataProof09.c52_length,JFx_DataProof09.c53_length,JFx_DataProof09.c54_length,JFx_DataProof09.c55_length,JFx_DataProof09.c56_length,JFx_DataProof09.c57_length,JFx_DataProof09.c58_length,JFx_DataProof09.c59_length,JFx_DataProof09.c60_length,JFx_DataProof09.c61_length,JFx_DataProof09.c62_length,JFx_DataProof09.c63_length,JFx_DataProof09.c64_length,JFx_DataProof09.c65_length,JFx_DataProof09.c66_length,JFx_DataProof09.c67_length,JFx_DataProof09.c68_length,JFx_DataProof09.c69_length,JFx_DataProof09.c70_length,JFx_DataProof09.c71_length,JFx_DataProof09.c72_length,JFx_DataProof09.c73_length,JFx_DataProof09.c74_length,JFx_DataProof09.c75_length,JFx_DataProof09.c76_length,JFx_DataProof09.c77_length,JFx_DataProof09.c78_length,JFx_DataProof09.c79_length,JFx_DataProof09.c80_length,JFx_DataProof09.c81_length,JFx_DataProof09.c82_length,JFx_DataProof09.c83_length,JFx_DataProof09.c84_length,JFx_DataProof09.c85_length,JFx_DataProof09.c86_length,JFx_DataProof09.c87_length,JFx_DataProof09.c88_length,JFx_DataProof09.c89_length,JFx_DataProof09.c90_length,JFx_DataProof09.c91_length,JFx_DataProof09.c92_length,JFx_DataProof09.c93_length,JFx_DataProof09.c94_length,JFx_DataProof09.c95_length,JFx_DataProof09.c96_length,JFx_DataProof09.c97_length,JFx_DataProof09.c98_length,JFx_DataProof09.c99_length,JFx_DataProof09.c100_length,JFx_DataProof09.c101_length,JFx_DataProof09.c102_length,JFx_DataProof09.c103_length,JFx_DataProof09.c104_length,JFx_DataProof09.c105_length,JFx_DataProof09.c106_length,JFx_DataProof09.c107_length,JFx_DataProof09.c108_length,JFx_DataProof09.c109_length,JFx_DataProof09.c110_length,JFx_DataProof09.c111_length,JFx_DataProof09.c112_length,JFx_DataProof09.c113_length,JFx_DataProof09.c114_length,JFx_DataProof09.c115_length,JFx_DataProof09.c116_length,JFx_DataProof09.c117_length,JFx_DataProof09.c118_length,JFx_DataProof09.c119_length,JFx_DataProof09.c120_length,JFx_DataProof09.c121_length,JFx_DataProof09.c122_length,JFx_DataProof09.c123_length,JFx_DataProof09.c124_length,JFx_DataProof09.c125_length,JFx_DataProof09.c126_length,JFx_DataProof09.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot2.value 928#usize 960#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 640) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 960 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 640 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 4099#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 640 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value020) :=
    JGm_TX2_View.value (s00 s) indices00 values00 640 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=640#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠4099#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨5843#u32,JGm_TX2_View.index (s00 s) indices00 values00 640 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s00 s).«at» 672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes2 0#usize 0#usize 1#usize 672#usize 3200#usize
    4099#u32 (encodeState value020) (encodeState (JGc_TX2_HashBytes.state [194,245,184,247,117,235,145,13,126,50,69,25,98,255,22,215,181,195,177,122,110,168,180,137,116,143,124,181,73,28,5,69])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read00
  simp only [show 4099#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls2.source030 D hash (s00 s) 1#usize 672#usize 4099#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 672 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 640 v00
      4099#u32 0#usize (encodeState value030) 672#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 5843#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 672 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value021) :=
    JGm_TX2_View.value (s01 s) indices01 values01 672 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=672#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠5843#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9220#u32,JGm_TX2_View.index (s01 s) indices01 values01 672 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s01 s).«at» 704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes2 1#usize 1#usize 2#usize 704#usize 3168#usize
    5843#u32 (encodeState value021) (encodeState (JGc_TX2_HashBytes.state [254,249,253,171,105,7,200,164,192,146,148,22,234,243,156,193,204,205,200,27,131,103,94,225,10,168,70,82,231,124,252,35])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read01
  simp only [show 5843#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls2.source031 D hash (s01 s) 2#usize 704#usize 5843#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 704 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 672 v01
      5843#u32 1#usize (encodeState value031) 704#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 9220#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 704 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value022) :=
    JGm_TX2_View.value (s02 s) indices02 values02 704 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=704#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠9220#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨9988#u32,JGm_TX2_View.index (s02 s) indices02 values02 704 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s02 s).«at» 736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes2 2#usize 2#usize 3#usize 736#usize 3136#usize
    9220#u32 (encodeState value022) (encodeState (JGc_TX2_HashBytes.state [186,93,169,162,221,9,97,47,195,23,151,178,51,170,82,124,130,6,105,43,70,227,136,131,203,240,135,148,160,124,113,200])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read02
  simp only [show 9220#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls2.source032 D hash (s02 s) 3#usize 736#usize 9220#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 736 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 704 v02
      9220#u32 2#usize (encodeState value032) 736#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 9988#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 736 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value023) :=
    JGm_TX2_View.value (s03 s) indices03 values03 736 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=736#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠9988#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨11491#u32,JGm_TX2_View.index (s03 s) indices03 values03 736 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s03 s).«at» 768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes2 3#usize 3#usize 4#usize 768#usize 3104#usize
    9988#u32 (encodeState value023) (encodeState (JGc_TX2_HashBytes.state [117,14,241,103,80,121,161,108,21,104,179,229,107,125,84,31,189,134,142,185,135,253,55,234,139,89,193,114,221,115,46,128])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read03
  simp only [show 9988#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls2.source033 D hash (s03 s) 4#usize 768#usize 9988#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 768 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 736 v03
      9988#u32 3#usize (encodeState value033) 768#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 11491#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 768 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value024) :=
    JGm_TX2_View.value (s04 s) indices04 values04 768 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=768#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠11491#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12019#u32,JGm_TX2_View.index (s04 s) indices04 values04 768 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s04 s).«at» 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes2 4#usize 4#usize 5#usize 800#usize 3072#usize
    11491#u32 (encodeState value024) (encodeState (JGc_TX2_HashBytes.state [252,199,160,112,92,68,47,54,9,188,58,105,45,11,24,100,63,52,109,70,105,61,240,30,194,73,210,110,30,137,146,5])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read04
  simp only [show 11491#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls2.source034 D hash (s04 s) 5#usize 800#usize 11491#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 800 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 768 v04
      11491#u32 4#usize (encodeState value034) 800#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 12019#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 800 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value025) :=
    JGm_TX2_View.value (s05 s) indices05 values05 800 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=800#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠12019#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨12068#u32,JGm_TX2_View.index (s05 s) indices05 values05 800 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s05 s).«at» 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes2 5#usize 5#usize 6#usize 832#usize 3040#usize
    12019#u32 (encodeState value025) (encodeState (JGc_TX2_HashBytes.state [235,50,176,191,189,100,44,247,120,2,40,116,130,231,48,6,150,118,123,187,248,252,9,165,185,26,191,183,209,65,102,221])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read05
  simp only [show 12019#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls2.source035 D hash (s05 s) 6#usize 832#usize 12019#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 832 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 800 v05
      12019#u32 5#usize (encodeState value035) 832#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 12068#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 832 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value026) :=
    JGm_TX2_View.value (s06 s) indices06 values06 832 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=832#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠12068#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13085#u32,JGm_TX2_View.index (s06 s) indices06 values06 832 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s06 s).«at» 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes2 6#usize 6#usize 7#usize 864#usize 3008#usize
    12068#u32 (encodeState value026) (encodeState (JGc_TX2_HashBytes.state [220,245,95,204,173,38,219,209,33,203,132,173,44,78,7,132,64,185,24,223,162,215,156,66,211,174,245,196,96,216,230,66])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read06
  simp only [show 12068#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls2.source036 D hash (s06 s) 7#usize 864#usize 12068#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 864 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 832 v06
      12068#u32 6#usize (encodeState value036) 864#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 13085#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 864 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value027) :=
    JGm_TX2_View.value (s07 s) indices07 values07 864 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=864#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠13085#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨13551#u32,JGm_TX2_View.index (s07 s) indices07 values07 864 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s07 s).«at» 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes2 7#usize 7#usize 8#usize 896#usize 2976#usize
    13085#u32 (encodeState value027) (encodeState (JGc_TX2_HashBytes.state [106,76,243,247,175,186,175,214,242,19,159,62,63,228,244,231,157,110,252,193,106,75,125,234,209,149,240,59,55,204,191,128])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read07
  simp only [show 13085#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls2.source037 D hash (s07 s) 8#usize 896#usize 13085#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 896 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 864 v07
      13085#u32 7#usize (encodeState value037) 896#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 13551#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 896 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value028) :=
    JGm_TX2_View.value (s08 s) indices08 values08 896 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=896#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠13551#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨15368#u32,JGm_TX2_View.index (s08 s) indices08 values08 896 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s08 s).«at» 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes2 8#usize 8#usize 9#usize 928#usize 2944#usize
    13551#u32 (encodeState value028) (encodeState (JGc_TX2_HashBytes.state [236,64,23,201,253,208,86,58,10,82,89,203,137,84,53,121,112,94,44,47,16,0,83,247,169,8,40,153,151,170,22,238])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read08
  simp only [show 13551#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls2.source038 D hash (s08 s) 9#usize 928#usize 13551#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 928 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 896 v08
      13551#u32 8#usize (encodeState value038) 928#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 15368#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 928 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value029) :=
    JGm_TX2_View.value (s09 s) indices09 values09 928 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=928#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠15368#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes2
      (s09 s).«at» 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes2 9#usize 9#usize 10#usize 960#usize 2912#usize
    15368#u32 (encodeState value029) (encodeState (JGc_TX2_HashBytes.state [202,189,29,169,70,123,183,226,47,76,15,140,170,67,27,238,204,183,171,51,116,132,60,183,181,124,58,4,43,84,219,250])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes2=3840#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length2
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length2];decide) read09
  simp only [show 15368#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls2.source039 D hash (s09 s) 10#usize 960#usize 15368#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 960 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 928 v09
      15368#u32 9#usize (encodeState value039) 960#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes2 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes2 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes2 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes2 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes2 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes2 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes2 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes2 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes2 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes2 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes2 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 960
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level2_02
end


end
