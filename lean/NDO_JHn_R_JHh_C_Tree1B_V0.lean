import NDO_JHn_R_JHh_C_Tree1B_L1
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
import NDO_JHn_R_JHh_C_Tree1A
import NDO_JHe_SHARealization
import Port4B_KeyDecode
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_00
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [65593#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
def values00 : List (Array U8 32#usize) := [encodeState value006,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 65593#u32 0#usize (encodeState value010) 32#usize
 def indices01 : List U32 := [32796#u32,93499#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value010,encodeState value000,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 93499#u32 1#usize (encodeState value011) 64#usize
 def indices02 : List U32 := [32796#u32,46749#u32,147529#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value001,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 147529#u32 2#usize (encodeState value012) 96#usize
 def indices03 : List U32 := [32796#u32,46749#u32,73764#u32,159813#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value009,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 159813#u32 3#usize (encodeState value013) 128#usize
 def indices04 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,183859#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value007,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 183859#u32 4#usize (encodeState value014) 160#usize
 def indices05 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,192317#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value005,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 192317#u32 5#usize (encodeState value015) 192#usize
 def indices06 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,193093#u32,209371#u32,216823#u32,245899#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value008,encodeState value004,encodeState value002,encodeState value003]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 193093#u32 6#usize (encodeState value016) 224#usize
 def indices07 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,209371#u32,216823#u32,245899#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value004,encodeState value002,encodeState value003]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 209371#u32 7#usize (encodeState value017) 256#usize
 def indices08 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,216823#u32,245899#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value002,encodeState value003]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 216823#u32 8#usize (encodeState value018) 288#usize
 def indices09 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,245899#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value003]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 245899#u32 9#usize (encodeState value019) 320#usize
 def indices10 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      0#usize 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 0#usize 32#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 0#usize 32#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 0).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33031).take 32)=(encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 0#usize 32#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      32#usize 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 32#usize 64#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 32#usize 64#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 32).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33063).take 32)=(encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 32#usize 64#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      64#usize 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 64#usize 96#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 64#usize 96#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 64).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33095).take 32)=(encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 64#usize 96#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      96#usize 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 96#usize 128#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 96#usize 128#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 96).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33127).take 32)=(encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 96#usize 128#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      128#usize 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 128#usize 160#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 128#usize 160#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 128).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33159).take 32)=(encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 128#usize 160#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      160#usize 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 160#usize 192#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 160#usize 192#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 160).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33191).take 32)=(encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 160#usize 192#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      192#usize 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 192#usize 224#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 192#usize 224#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 192).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33223).take 32)=(encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 192#usize 224#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      224#usize 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 224#usize 256#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 224#usize 256#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 224).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33255).take 32)=(encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 224#usize 256#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      256#usize 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 256#usize 288#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 256#usize 288#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 256).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33287).take 32)=(encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 256#usize 288#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      288#usize 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 288#usize 320#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 288#usize 320#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 288).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33319).take 32)=(encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 288#usize 320#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 0) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 320 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 0 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 65593#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value006) :=
    JGm_TX2_View.value (s00 s) indices00 values00 0 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=0#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠65593#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨93499#u32,JGm_TX2_View.index (s00 s) indices00 values00 0 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 32#usize)=ok (encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 32#usize 4416#usize
    65593#u32 (encodeState value006) (encodeState (JGc_TX2_HashBytes.state [84,158,189,163,7,211,150,118,46,159,127,12,244,157,167,96,164,240,68,44,151,232,222,236,240,147,88,216,134,56,255,201])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 65593#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source010 D hash (s00 s) 1#usize 32#usize 65593#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 32 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 0 v00
      65593#u32 0#usize (encodeState value010) 32#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 93499#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value000) :=
    JGm_TX2_View.value (s01 s) indices01 values01 32 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=32#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠93499#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨147529#u32,JGm_TX2_View.index (s01 s) indices01 values01 32 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 64#usize)=ok (encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 64#usize 4384#usize
    93499#u32 (encodeState value000) (encodeState (JGc_TX2_HashBytes.state [87,201,97,142,46,240,30,62,247,57,210,209,11,218,107,245,200,85,9,191,193,152,235,191,239,43,233,153,92,147,12,22])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 93499#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source011 D hash (s01 s) 2#usize 64#usize 93499#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 64 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 32 v01
      93499#u32 1#usize (encodeState value011) 64#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 147529#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value001) :=
    JGm_TX2_View.value (s02 s) indices02 values02 64 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=64#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠147529#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨159813#u32,JGm_TX2_View.index (s02 s) indices02 values02 64 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 96#usize)=ok (encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 96#usize 4352#usize
    147529#u32 (encodeState value001) (encodeState (JGc_TX2_HashBytes.state [126,244,47,162,206,176,63,208,66,80,97,27,124,150,156,29,16,125,4,24,229,40,80,226,50,22,217,21,9,118,223,64])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 147529#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source012 D hash (s02 s) 3#usize 96#usize 147529#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 96 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 64 v02
      147529#u32 2#usize (encodeState value012) 96#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 159813#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value009) :=
    JGm_TX2_View.value (s03 s) indices03 values03 96 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=96#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠159813#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨183859#u32,JGm_TX2_View.index (s03 s) indices03 values03 96 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 128#usize)=ok (encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 128#usize 4320#usize
    159813#u32 (encodeState value009) (encodeState (JGc_TX2_HashBytes.state [105,207,46,68,125,195,225,145,182,7,102,115,151,53,228,97,66,255,193,10,177,180,57,243,141,165,117,4,62,94,100,227])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 159813#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source013 D hash (s03 s) 4#usize 128#usize 159813#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 128 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 96 v03
      159813#u32 3#usize (encodeState value013) 128#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 183859#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value007) :=
    JGm_TX2_View.value (s04 s) indices04 values04 128 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=128#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠183859#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨192317#u32,JGm_TX2_View.index (s04 s) indices04 values04 128 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 160#usize)=ok (encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 160#usize 4288#usize
    183859#u32 (encodeState value007) (encodeState (JGc_TX2_HashBytes.state [178,45,27,133,141,100,37,222,96,165,67,100,140,205,14,251,78,74,113,201,225,78,242,12,210,165,12,143,151,125,240,161])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 183859#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source014 D hash (s04 s) 5#usize 160#usize 183859#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 160 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 128 v04
      183859#u32 4#usize (encodeState value014) 160#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 192317#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value005) :=
    JGm_TX2_View.value (s05 s) indices05 values05 160 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=160#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠192317#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨193093#u32,JGm_TX2_View.index (s05 s) indices05 values05 160 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 192#usize)=ok (encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 192#usize 4256#usize
    192317#u32 (encodeState value005) (encodeState (JGc_TX2_HashBytes.state [208,201,87,103,45,128,36,40,65,168,170,172,133,87,105,49,90,3,53,79,63,150,156,172,52,208,232,217,131,11,191,68])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 192317#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source015 D hash (s05 s) 6#usize 192#usize 192317#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 192 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 160 v05
      192317#u32 5#usize (encodeState value015) 192#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 193093#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value008) :=
    JGm_TX2_View.value (s06 s) indices06 values06 192 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=192#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠193093#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨209371#u32,JGm_TX2_View.index (s06 s) indices06 values06 192 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 224#usize)=ok (encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 224#usize 4224#usize
    193093#u32 (encodeState value008) (encodeState (JGc_TX2_HashBytes.state [58,250,234,236,124,53,147,155,154,165,220,179,164,49,96,165,20,23,164,50,251,216,34,12,121,250,222,56,113,154,22,180])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 193093#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source016 D hash (s06 s) 7#usize 224#usize 193093#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 224 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 192 v06
      193093#u32 6#usize (encodeState value016) 224#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 209371#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value004) :=
    JGm_TX2_View.value (s07 s) indices07 values07 224 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=224#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠209371#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨216823#u32,JGm_TX2_View.index (s07 s) indices07 values07 224 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 256#usize)=ok (encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 256#usize 4192#usize
    209371#u32 (encodeState value004) (encodeState (JGc_TX2_HashBytes.state [229,11,75,185,166,129,153,153,211,153,179,106,3,80,171,146,89,184,131,52,57,244,191,194,9,142,23,33,62,19,35,156])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 209371#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source017 D hash (s07 s) 8#usize 256#usize 209371#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 256 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 224 v07
      209371#u32 7#usize (encodeState value017) 256#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 216823#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value002) :=
    JGm_TX2_View.value (s08 s) indices08 values08 256 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=256#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠216823#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨245899#u32,JGm_TX2_View.index (s08 s) indices08 values08 256 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 288#usize)=ok (encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 288#usize 4160#usize
    216823#u32 (encodeState value002) (encodeState (JGc_TX2_HashBytes.state [232,135,117,237,45,118,87,95,67,116,77,226,109,208,88,160,202,241,38,170,96,84,230,88,96,117,190,107,137,190,145,40])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 216823#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source018 D hash (s08 s) 9#usize 288#usize 216823#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 288 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 256 v08
      216823#u32 8#usize (encodeState value018) 288#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 245899#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value003) :=
    JGm_TX2_View.value (s09 s) indices09 values09 288 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=288#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠245899#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 320#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 320#usize 4128#usize
    245899#u32 (encodeState value003) (encodeState (JGc_TX2_HashBytes.state [198,199,120,82,46,88,27,188,251,85,66,197,217,209,68,171,23,178,127,119,231,149,16,43,202,127,140,173,252,101,60,6])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 245899#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source019 D hash (s09 s) 10#usize 320#usize 245899#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 320 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 288 v09
      245899#u32 9#usize (encodeState value019) 320#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 320
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_00
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_01
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [32796#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
def values00 : List (Array U8 32#usize) := [encodeState value010,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 32796#u32 0#usize (encodeState value020) 352#usize
 def indices01 : List U32 := [16398#u32,46749#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value020,encodeState value011,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 46749#u32 1#usize (encodeState value021) 384#usize
 def indices02 : List U32 := [16398#u32,23374#u32,73764#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value012,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 73764#u32 2#usize (encodeState value022) 416#usize
 def indices03 : List U32 := [16398#u32,23374#u32,36882#u32,79906#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value013,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 79906#u32 3#usize (encodeState value023) 448#usize
 def indices04 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,91929#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value014,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 91929#u32 4#usize (encodeState value024) 480#usize
 def indices05 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,96158#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value015,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 96158#u32 5#usize (encodeState value025) 512#usize
 def indices06 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,96546#u32,104685#u32,108411#u32,122949#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value016,encodeState value017,encodeState value018,encodeState value019]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 96546#u32 6#usize (encodeState value026) 544#usize
 def indices07 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,104685#u32,108411#u32,122949#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value017,encodeState value018,encodeState value019]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 104685#u32 7#usize (encodeState value027) 576#usize
 def indices08 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,108411#u32,122949#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value018,encodeState value019]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 108411#u32 8#usize (encodeState value028) 608#usize
 def indices09 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,122949#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value019]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 122949#u32 9#usize (encodeState value029) 640#usize
 def indices10 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      320#usize 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 320#usize 352#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 320#usize 352#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 320).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33351).take 32)=(encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 320#usize 352#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      352#usize 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 352#usize 384#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 352#usize 384#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 352).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33383).take 32)=(encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 352#usize 384#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      384#usize 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 384#usize 416#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 384#usize 416#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 384).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33415).take 32)=(encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 384#usize 416#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      416#usize 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 416#usize 448#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 416#usize 448#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 416).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33447).take 32)=(encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 416#usize 448#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      448#usize 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 448#usize 480#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 448#usize 480#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 448).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33479).take 32)=(encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 448#usize 480#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      480#usize 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 480#usize 512#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 480#usize 512#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 480).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33511).take 32)=(encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 480#usize 512#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      512#usize 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 512#usize 544#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 512#usize 544#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 512).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33543).take 32)=(encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 512#usize 544#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      544#usize 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 544#usize 576#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 544#usize 576#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 544).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33575).take 32)=(encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 544#usize 576#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      576#usize 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 576#usize 608#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 576#usize 608#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 576).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33607).take 32)=(encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 576#usize 608#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      608#usize 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 608#usize 640#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 608#usize 640#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 608).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33639).take 32)=(encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 608#usize 640#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 320) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 640 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 320 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 32796#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value010) :=
    JGm_TX2_View.value (s00 s) indices00 values00 320 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=320#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠32796#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨46749#u32,JGm_TX2_View.index (s00 s) indices00 values00 320 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 352#usize)=ok (encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 352#usize 4096#usize
    32796#u32 (encodeState value010) (encodeState (JGc_TX2_HashBytes.state [226,19,230,186,28,97,100,40,122,60,48,235,166,167,156,189,127,126,176,209,146,207,129,60,75,115,18,146,199,245,51,199])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 32796#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source020 D hash (s00 s) 1#usize 352#usize 32796#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 352 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 320 v00
      32796#u32 0#usize (encodeState value020) 352#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 46749#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value011) :=
    JGm_TX2_View.value (s01 s) indices01 values01 352 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=352#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠46749#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨73764#u32,JGm_TX2_View.index (s01 s) indices01 values01 352 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 384#usize)=ok (encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 384#usize 4064#usize
    46749#u32 (encodeState value011) (encodeState (JGc_TX2_HashBytes.state [53,199,117,75,221,203,227,135,140,20,26,44,148,40,245,6,247,144,199,69,152,25,40,59,8,112,100,10,148,1,240,224])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 46749#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source021 D hash (s01 s) 2#usize 384#usize 46749#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 384 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 352 v01
      46749#u32 1#usize (encodeState value021) 384#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 73764#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value012) :=
    JGm_TX2_View.value (s02 s) indices02 values02 384 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=384#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠73764#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨79906#u32,JGm_TX2_View.index (s02 s) indices02 values02 384 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 416#usize)=ok (encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 416#usize 4032#usize
    73764#u32 (encodeState value012) (encodeState (JGc_TX2_HashBytes.state [192,50,200,213,36,199,105,201,154,83,49,107,171,199,140,138,138,25,255,180,249,204,200,221,50,43,166,214,67,36,110,16])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 73764#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source022 D hash (s02 s) 3#usize 416#usize 73764#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 416 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 384 v02
      73764#u32 2#usize (encodeState value022) 416#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 79906#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value013) :=
    JGm_TX2_View.value (s03 s) indices03 values03 416 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=416#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠79906#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨91929#u32,JGm_TX2_View.index (s03 s) indices03 values03 416 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 448#usize)=ok (encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 448#usize 4000#usize
    79906#u32 (encodeState value013) (encodeState (JGc_TX2_HashBytes.state [102,110,213,2,148,96,173,189,56,93,84,101,64,44,166,50,155,9,114,234,56,56,211,60,155,126,100,123,86,255,245,207])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 79906#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source023 D hash (s03 s) 4#usize 448#usize 79906#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 448 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 416 v03
      79906#u32 3#usize (encodeState value023) 448#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 91929#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value014) :=
    JGm_TX2_View.value (s04 s) indices04 values04 448 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=448#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠91929#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨96158#u32,JGm_TX2_View.index (s04 s) indices04 values04 448 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 480#usize)=ok (encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 480#usize 3968#usize
    91929#u32 (encodeState value014) (encodeState (JGc_TX2_HashBytes.state [207,254,248,226,47,19,54,49,165,112,36,160,160,101,28,252,240,13,181,65,153,32,3,78,22,59,184,81,253,195,95,153])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 91929#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source024 D hash (s04 s) 5#usize 480#usize 91929#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 480 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 448 v04
      91929#u32 4#usize (encodeState value024) 480#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 96158#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value015) :=
    JGm_TX2_View.value (s05 s) indices05 values05 480 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=480#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠96158#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨96546#u32,JGm_TX2_View.index (s05 s) indices05 values05 480 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 512#usize)=ok (encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 512#usize 3936#usize
    96158#u32 (encodeState value015) (encodeState (JGc_TX2_HashBytes.state [118,182,6,74,103,244,136,114,84,255,217,64,189,71,61,128,226,133,217,73,78,68,236,158,199,227,240,136,1,108,57,83])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 96158#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source025 D hash (s05 s) 6#usize 512#usize 96158#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 512 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 480 v05
      96158#u32 5#usize (encodeState value025) 512#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 96546#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value016) :=
    JGm_TX2_View.value (s06 s) indices06 values06 512 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=512#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠96546#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨104685#u32,JGm_TX2_View.index (s06 s) indices06 values06 512 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 544#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 544#usize 3904#usize
    96546#u32 (encodeState value016) (encodeState (JGc_TX2_HashBytes.state [198,145,218,11,27,71,231,58,41,252,108,230,167,179,48,30,19,243,203,144,105,210,9,80,77,183,232,151,137,4,170,15])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 96546#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source026 D hash (s06 s) 7#usize 544#usize 96546#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 544 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 512 v06
      96546#u32 6#usize (encodeState value026) 544#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 104685#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value017) :=
    JGm_TX2_View.value (s07 s) indices07 values07 544 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=544#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠104685#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨108411#u32,JGm_TX2_View.index (s07 s) indices07 values07 544 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 576#usize)=ok (encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 576#usize 3872#usize
    104685#u32 (encodeState value017) (encodeState (JGc_TX2_HashBytes.state [104,141,228,117,121,171,3,4,176,4,107,28,254,224,219,29,112,25,96,120,70,213,98,52,25,175,170,185,190,225,223,156])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 104685#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source027 D hash (s07 s) 8#usize 576#usize 104685#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 576 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 544 v07
      104685#u32 7#usize (encodeState value027) 576#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 108411#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value018) :=
    JGm_TX2_View.value (s08 s) indices08 values08 576 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=576#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠108411#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨122949#u32,JGm_TX2_View.index (s08 s) indices08 values08 576 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 608#usize)=ok (encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 608#usize 3840#usize
    108411#u32 (encodeState value018) (encodeState (JGc_TX2_HashBytes.state [86,28,233,120,193,72,153,62,145,245,239,192,86,31,200,86,29,20,129,186,93,27,187,6,64,75,180,174,8,117,228,16])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 108411#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source028 D hash (s08 s) 9#usize 608#usize 108411#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 608 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 576 v08
      108411#u32 8#usize (encodeState value028) 608#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 122949#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value019) :=
    JGm_TX2_View.value (s09 s) indices09 values09 608 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=608#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠122949#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 640#usize)=ok (encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 640#usize 3808#usize
    122949#u32 (encodeState value019) (encodeState (JGc_TX2_HashBytes.state [46,114,18,158,240,245,37,120,114,167,15,134,67,123,175,250,230,84,253,40,11,47,196,152,226,249,239,35,86,182,35,30])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 122949#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source029 D hash (s09 s) 10#usize 640#usize 122949#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 640 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 608 v09
      122949#u32 9#usize (encodeState value029) 640#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 640
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_01
end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace AspisR1.JHh_C_Gu_Level1_02
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.SqueezeOracleBridge
open JHh_C_Gr_M1Roots
attribute [local irreducible] JFx_NativeBytes.proof JGy_G_JGu_Supplied.nodes1
def indices00 : List U32 := [16398#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
def values00 : List (Array U8 32#usize) := [encodeState value020,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s00 (s : reference.Scratch) := s
def s01 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s00 s) 16398#u32 0#usize (encodeState value030) 672#usize
 def indices01 : List U32 := [8199#u32,23374#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values01 : List (Array U8 32#usize) := [encodeState value030,encodeState value021,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s02 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s01 s) 23374#u32 1#usize (encodeState value031) 704#usize
 def indices02 : List U32 := [8199#u32,11687#u32,36882#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values02 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value022,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s03 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s02 s) 36882#u32 2#usize (encodeState value032) 736#usize
 def indices03 : List U32 := [8199#u32,11687#u32,18441#u32,39953#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values03 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value023,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s04 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s03 s) 39953#u32 3#usize (encodeState value033) 768#usize
 def indices04 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,45964#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values04 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value024,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s05 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s04 s) 45964#u32 4#usize (encodeState value034) 800#usize
 def indices05 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,48079#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values05 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value025,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s06 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s05 s) 48079#u32 5#usize (encodeState value035) 832#usize
 def indices06 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,48273#u32,52342#u32,54205#u32,61474#u32]
 def values06 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value026,encodeState value027,encodeState value028,encodeState value029]
def s07 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s06 s) 48273#u32 6#usize (encodeState value036) 864#usize
 def indices07 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,52342#u32,54205#u32,61474#u32]
 def values07 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value027,encodeState value028,encodeState value029]
def s08 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s07 s) 52342#u32 7#usize (encodeState value037) 896#usize
 def indices08 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,54205#u32,61474#u32]
 def values08 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value028,encodeState value029]
def s09 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s08 s) 54205#u32 8#usize (encodeState value038) 928#usize
 def indices09 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,61474#u32]
 def values09 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value029]
def s10 (s : reference.Scratch) : reference.Scratch :=
  JGy_G_JGk_TX2_ParentWrite.after (s09 s) 61474#u32 9#usize (encodeState value039) 960#usize
 def indices10 : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def values10 : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
def output (s : reference.Scratch) : reference.Scratch := {s10 s with n:=10#usize}
 def indicesOut : List U32 := [8199#u32,11687#u32,18441#u32,19976#u32,22982#u32,24039#u32,24136#u32,26171#u32,27102#u32,30737#u32]
 def valuesOut : List (Array U8 32#usize) := [encodeState value030,encodeState value031,encodeState value032,encodeState value033,encodeState value034,encodeState value035,encodeState value036,encodeState value037,encodeState value038,encodeState value039]
theorem read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      640#usize 672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 640#usize 672#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 640#usize 672#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 640).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33671).take 32)=(encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 640#usize 672#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])).property];decide)
  exact same ▸ run
#print axioms read00
theorem read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      672#usize 704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 672#usize 704#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 672#usize 704#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 672).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33703).take 32)=(encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 672#usize 704#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])).property];decide)
  exact same ▸ run
#print axioms read01
theorem read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      704#usize 736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 704#usize 736#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 704#usize 736#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 704).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33735).take 32)=(encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 704#usize 736#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])).property];decide)
  exact same ▸ run
#print axioms read02
theorem read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      736#usize 768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 736#usize 768#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 736#usize 768#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 736).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33767).take 32)=(encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 736#usize 768#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])).property];decide)
  exact same ▸ run
#print axioms read03
theorem read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      768#usize 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 768#usize 800#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 768#usize 800#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 768).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33799).take 32)=(encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 768#usize 800#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])).property];decide)
  exact same ▸ run
#print axioms read04
theorem read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      800#usize 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 800#usize 832#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 800#usize 832#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 800).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33831).take 32)=(encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 800#usize 832#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])).property];decide)
  exact same ▸ run
#print axioms read05
theorem read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      832#usize 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 832#usize 864#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 832#usize 864#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 832).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33863).take 32)=(encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 832#usize 864#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])).property];decide)
  exact same ▸ run
#print axioms read06
theorem read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      864#usize 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 864#usize 896#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 864#usize 896#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 864).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33895).take 32)=(encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 864#usize 896#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])).property];decide)
  exact same ▸ run
#print axioms read07
theorem read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      896#usize 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 896#usize 928#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 896#usize 928#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 896).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33927).take 32)=(encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 896#usize 928#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])).property];decide)
  exact same ▸ run
#print axioms read08
theorem read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      928#usize 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])) := by
  unfold JGy_G_JGu_Supplied.nodes1
  rw [JGy_G_JGm_TX2_Supplied.sub_prefix JGp_Slot1.value 4416#usize 928#usize 960#usize (by decide) (by decide)]
  have phys : (MultiproofConeSlices.sub JGp_Slot1.value 928#usize 960#usize).val=
      (encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])).val := by
    change (((JFw_Frames.window 33031 4672).val.drop 928).take 32)=_
    rw [JFw_Frames.window,JFq_Range.nested _ _ _ _ _ (by decide)]
    change ((JFx_NativeBytes.proof.val.drop 33959).take 32)=(encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])).val
    simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    simp only [JFx_DataProof08.bytes,JFx_DataProof08.c00_length,JFx_DataProof08.c01_length,JFx_DataProof08.c02_length,JFx_DataProof08.c03_length,JFx_DataProof08.c04_length,JFx_DataProof08.c05_length,JFx_DataProof08.c06_length,JFx_DataProof08.c07_length,JFx_DataProof08.c08_length,JFx_DataProof08.c09_length,JFx_DataProof08.c10_length,JFx_DataProof08.c11_length,JFx_DataProof08.c12_length,JFx_DataProof08.c13_length,JFx_DataProof08.c14_length,JFx_DataProof08.c15_length,JFx_DataProof08.c16_length,JFx_DataProof08.c17_length,JFx_DataProof08.c18_length,JFx_DataProof08.c19_length,JFx_DataProof08.c20_length,JFx_DataProof08.c21_length,JFx_DataProof08.c22_length,JFx_DataProof08.c23_length,JFx_DataProof08.c24_length,JFx_DataProof08.c25_length,JFx_DataProof08.c26_length,JFx_DataProof08.c27_length,JFx_DataProof08.c28_length,JFx_DataProof08.c29_length,JFx_DataProof08.c30_length,JFx_DataProof08.c31_length,JFx_DataProof08.c32_length,JFx_DataProof08.c33_length,JFx_DataProof08.c34_length,JFx_DataProof08.c35_length,JFx_DataProof08.c36_length,JFx_DataProof08.c37_length,JFx_DataProof08.c38_length,JFx_DataProof08.c39_length,JFx_DataProof08.c40_length,JFx_DataProof08.c41_length,JFx_DataProof08.c42_length,JFx_DataProof08.c43_length,JFx_DataProof08.c44_length,JFx_DataProof08.c45_length,JFx_DataProof08.c46_length,JFx_DataProof08.c47_length,JFx_DataProof08.c48_length,JFx_DataProof08.c49_length,JFx_DataProof08.c50_length,JFx_DataProof08.c51_length,JFx_DataProof08.c52_length,JFx_DataProof08.c53_length,JFx_DataProof08.c54_length,JFx_DataProof08.c55_length,JFx_DataProof08.c56_length,JFx_DataProof08.c57_length,JFx_DataProof08.c58_length,JFx_DataProof08.c59_length,JFx_DataProof08.c60_length,JFx_DataProof08.c61_length,JFx_DataProof08.c62_length,JFx_DataProof08.c63_length,JFx_DataProof08.c64_length,JFx_DataProof08.c65_length,JFx_DataProof08.c66_length,JFx_DataProof08.c67_length,JFx_DataProof08.c68_length,JFx_DataProof08.c69_length,JFx_DataProof08.c70_length,JFx_DataProof08.c71_length,JFx_DataProof08.c72_length,JFx_DataProof08.c73_length,JFx_DataProof08.c74_length,JFx_DataProof08.c75_length,JFx_DataProof08.c76_length,JFx_DataProof08.c77_length,JFx_DataProof08.c78_length,JFx_DataProof08.c79_length,JFx_DataProof08.c80_length,JFx_DataProof08.c81_length,JFx_DataProof08.c82_length,JFx_DataProof08.c83_length,JFx_DataProof08.c84_length,JFx_DataProof08.c85_length,JFx_DataProof08.c86_length,JFx_DataProof08.c87_length,JFx_DataProof08.c88_length,JFx_DataProof08.c89_length,JFx_DataProof08.c90_length,JFx_DataProof08.c91_length,JFx_DataProof08.c92_length,JFx_DataProof08.c93_length,JFx_DataProof08.c94_length,JFx_DataProof08.c95_length,JFx_DataProof08.c96_length,JFx_DataProof08.c97_length,JFx_DataProof08.c98_length,JFx_DataProof08.c99_length,JFx_DataProof08.c100_length,JFx_DataProof08.c101_length,JFx_DataProof08.c102_length,JFx_DataProof08.c103_length,JFx_DataProof08.c104_length,JFx_DataProof08.c105_length,JFx_DataProof08.c106_length,JFx_DataProof08.c107_length,JFx_DataProof08.c108_length,JFx_DataProof08.c109_length,JFx_DataProof08.c110_length,JFx_DataProof08.c111_length,JFx_DataProof08.c112_length,JFx_DataProof08.c113_length,JFx_DataProof08.c114_length,JFx_DataProof08.c115_length,JFx_DataProof08.c116_length,JFx_DataProof08.c117_length,JFx_DataProof08.c118_length,JFx_DataProof08.c119_length,JFx_DataProof08.c120_length,JFx_DataProof08.c121_length,JFx_DataProof08.c122_length,JFx_DataProof08.c123_length,JFx_DataProof08.c124_length,JFx_DataProof08.c125_length,JFx_DataProof08.c126_length,JFx_DataProof08.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
    rfl
  obtain ⟨chunk,run,bytes⟩ := MultiproofConeRead32.read32_total
    (MultiproofConeSlices.sub JGp_Slot1.value 928#usize 960#usize)
    (by rw [phys,(encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])).property];decide)
  have same : chunk=encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215]) := by
    apply Subtype.ext
    rw [bytes,phys]
    exact List.take_of_length_le (by rw [(encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])).property];decide)
  exact same ▸ run
#print axioms read09
 theorem source {Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (view : JGm_TX2_View.View s indices00 values00 640) :
    reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      s JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=ok (.Done (output s)) ∧
    JGm_TX2_View.View (output s) indicesOut valuesOut 960 := by
  have v00 : JGm_TX2_View.View (s00 s) indices00 values00 640 := view
  have ri00 : Array.index_usize (s00 s).idx 0#usize=ok 16398#u32 :=
    JGm_TX2_View.index (s00 s) indices00 values00 640 v00 0#usize (by decide)
  have rv00 : Array.index_usize (s00 s).val 0#usize=ok (encodeState value020) :=
    JGm_TX2_View.value (s00 s) indices00 values00 640 v00 0#usize (by decide)
  have active00 : 0#usize<(s00 s).n := by
    change (0:Nat)<(s00 s).n.val
    rw [v00.size]
    decide
  have cursor00 : (s00 s).«at»=640#usize := UScalar.eq_of_val_eq v00.at_eq
  have unpaired00 : ∀ more : 1#usize<(s00 s).n,
      ∃ other,Array.index_usize (s00 s).idx 1#usize=ok other ∧ other≠16398#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨23374#u32,JGm_TX2_View.index (s00 s) indices00 values00 640 v00 1#usize (by decide),by decide⟩
  have read00 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s00 s).«at» 672#usize)=ok (encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])) := by
    rw [cursor00]
    exact read00
  have selected00 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s)
    JGy_G_JGu_Supplied.nodes1 0#usize 0#usize 1#usize 672#usize 3776#usize
    16398#u32 (encodeState value020) (encodeState (JGc_TX2_HashBytes.state [161,76,3,159,191,249,90,238,12,33,36,222,12,85,198,154,218,16,194,33,132,91,57,18,102,89,24,129,206,192,84,2])) ri00 rv00
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired00
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor00];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor00];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor00];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read00
  simp only [show 16398#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected00
  have row00 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize=
        ok (.Next (s01 s) 1#usize 1#usize) := by
    rw [selected00]
    exact JHh_C_Gu_ParentCalls1.source030 D hash (s00 s) 1#usize 672#usize 16398#u32 0#usize (by decide)
  have v01 : JGm_TX2_View.View (s01 s) indices01 values01 672 := by
    have v := JGm_TX2_View.after (s00 s) indices00 values00 640 v00
      16398#u32 0#usize (encodeState value030) 672#usize (by decide)
    exact v
  have ri01 : Array.index_usize (s01 s).idx 1#usize=ok 23374#u32 :=
    JGm_TX2_View.index (s01 s) indices01 values01 672 v01 1#usize (by decide)
  have rv01 : Array.index_usize (s01 s).val 1#usize=ok (encodeState value021) :=
    JGm_TX2_View.value (s01 s) indices01 values01 672 v01 1#usize (by decide)
  have active01 : 1#usize<(s01 s).n := by
    change (1:Nat)<(s01 s).n.val
    rw [v01.size]
    decide
  have cursor01 : (s01 s).«at»=672#usize := UScalar.eq_of_val_eq v01.at_eq
  have unpaired01 : ∀ more : 2#usize<(s01 s).n,
      ∃ other,Array.index_usize (s01 s).idx 2#usize=ok other ∧ other≠23374#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨36882#u32,JGm_TX2_View.index (s01 s) indices01 values01 672 v01 2#usize (by decide),by decide⟩
  have read01 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s01 s).«at» 704#usize)=ok (encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])) := by
    rw [cursor01]
    exact read01
  have selected01 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s)
    JGy_G_JGu_Supplied.nodes1 1#usize 1#usize 2#usize 704#usize 3744#usize
    23374#u32 (encodeState value021) (encodeState (JGc_TX2_HashBytes.state [150,245,179,73,238,203,63,9,99,117,193,114,224,59,215,81,139,40,94,196,154,161,204,163,131,194,211,158,164,68,7,147])) ri01 rv01
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired01
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor01];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor01];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor01];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read01
  simp only [show 23374#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected01
  have row01 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize=
        ok (.Next (s02 s) 2#usize 2#usize) := by
    rw [selected01]
    exact JHh_C_Gu_ParentCalls1.source031 D hash (s01 s) 2#usize 704#usize 23374#u32 1#usize (by decide)
  have v02 : JGm_TX2_View.View (s02 s) indices02 values02 704 := by
    have v := JGm_TX2_View.after (s01 s) indices01 values01 672 v01
      23374#u32 1#usize (encodeState value031) 704#usize (by decide)
    exact v
  have ri02 : Array.index_usize (s02 s).idx 2#usize=ok 36882#u32 :=
    JGm_TX2_View.index (s02 s) indices02 values02 704 v02 2#usize (by decide)
  have rv02 : Array.index_usize (s02 s).val 2#usize=ok (encodeState value022) :=
    JGm_TX2_View.value (s02 s) indices02 values02 704 v02 2#usize (by decide)
  have active02 : 2#usize<(s02 s).n := by
    change (2:Nat)<(s02 s).n.val
    rw [v02.size]
    decide
  have cursor02 : (s02 s).«at»=704#usize := UScalar.eq_of_val_eq v02.at_eq
  have unpaired02 : ∀ more : 3#usize<(s02 s).n,
      ∃ other,Array.index_usize (s02 s).idx 3#usize=ok other ∧ other≠36882#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨39953#u32,JGm_TX2_View.index (s02 s) indices02 values02 704 v02 3#usize (by decide),by decide⟩
  have read02 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s02 s).«at» 736#usize)=ok (encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])) := by
    rw [cursor02]
    exact read02
  have selected02 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s)
    JGy_G_JGu_Supplied.nodes1 2#usize 2#usize 3#usize 736#usize 3712#usize
    36882#u32 (encodeState value022) (encodeState (JGc_TX2_HashBytes.state [97,255,106,209,39,206,184,200,255,182,229,243,150,159,37,202,105,5,207,52,192,189,18,106,9,249,42,77,128,132,228,204])) ri02 rv02
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired02
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor02];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor02];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor02];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read02
  simp only [show 36882#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected02
  have row02 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize=
        ok (.Next (s03 s) 3#usize 3#usize) := by
    rw [selected02]
    exact JHh_C_Gu_ParentCalls1.source032 D hash (s02 s) 3#usize 736#usize 36882#u32 2#usize (by decide)
  have v03 : JGm_TX2_View.View (s03 s) indices03 values03 736 := by
    have v := JGm_TX2_View.after (s02 s) indices02 values02 704 v02
      36882#u32 2#usize (encodeState value032) 736#usize (by decide)
    exact v
  have ri03 : Array.index_usize (s03 s).idx 3#usize=ok 39953#u32 :=
    JGm_TX2_View.index (s03 s) indices03 values03 736 v03 3#usize (by decide)
  have rv03 : Array.index_usize (s03 s).val 3#usize=ok (encodeState value023) :=
    JGm_TX2_View.value (s03 s) indices03 values03 736 v03 3#usize (by decide)
  have active03 : 3#usize<(s03 s).n := by
    change (3:Nat)<(s03 s).n.val
    rw [v03.size]
    decide
  have cursor03 : (s03 s).«at»=736#usize := UScalar.eq_of_val_eq v03.at_eq
  have unpaired03 : ∀ more : 4#usize<(s03 s).n,
      ∃ other,Array.index_usize (s03 s).idx 4#usize=ok other ∧ other≠39953#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨45964#u32,JGm_TX2_View.index (s03 s) indices03 values03 736 v03 4#usize (by decide),by decide⟩
  have read03 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s03 s).«at» 768#usize)=ok (encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])) := by
    rw [cursor03]
    exact read03
  have selected03 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s)
    JGy_G_JGu_Supplied.nodes1 3#usize 3#usize 4#usize 768#usize 3680#usize
    39953#u32 (encodeState value023) (encodeState (JGc_TX2_HashBytes.state [198,117,40,249,115,8,80,114,136,28,25,209,63,143,53,34,247,134,30,13,179,145,39,114,51,86,73,45,212,147,188,0])) ri03 rv03
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired03
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor03];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor03];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor03];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read03
  simp only [show 39953#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected03
  have row03 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize=
        ok (.Next (s04 s) 4#usize 4#usize) := by
    rw [selected03]
    exact JHh_C_Gu_ParentCalls1.source033 D hash (s03 s) 4#usize 768#usize 39953#u32 3#usize (by decide)
  have v04 : JGm_TX2_View.View (s04 s) indices04 values04 768 := by
    have v := JGm_TX2_View.after (s03 s) indices03 values03 736 v03
      39953#u32 3#usize (encodeState value033) 768#usize (by decide)
    exact v
  have ri04 : Array.index_usize (s04 s).idx 4#usize=ok 45964#u32 :=
    JGm_TX2_View.index (s04 s) indices04 values04 768 v04 4#usize (by decide)
  have rv04 : Array.index_usize (s04 s).val 4#usize=ok (encodeState value024) :=
    JGm_TX2_View.value (s04 s) indices04 values04 768 v04 4#usize (by decide)
  have active04 : 4#usize<(s04 s).n := by
    change (4:Nat)<(s04 s).n.val
    rw [v04.size]
    decide
  have cursor04 : (s04 s).«at»=768#usize := UScalar.eq_of_val_eq v04.at_eq
  have unpaired04 : ∀ more : 5#usize<(s04 s).n,
      ∃ other,Array.index_usize (s04 s).idx 5#usize=ok other ∧ other≠45964#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨48079#u32,JGm_TX2_View.index (s04 s) indices04 values04 768 v04 5#usize (by decide),by decide⟩
  have read04 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s04 s).«at» 800#usize)=ok (encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])) := by
    rw [cursor04]
    exact read04
  have selected04 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s)
    JGy_G_JGu_Supplied.nodes1 4#usize 4#usize 5#usize 800#usize 3648#usize
    45964#u32 (encodeState value024) (encodeState (JGc_TX2_HashBytes.state [173,160,200,2,87,10,143,76,228,213,202,85,241,88,184,137,184,213,12,133,110,196,125,206,65,42,21,23,14,224,135,18])) ri04 rv04
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired04
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor04];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor04];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor04];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read04
  simp only [show 45964#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected04
  have row04 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize=
        ok (.Next (s05 s) 5#usize 5#usize) := by
    rw [selected04]
    exact JHh_C_Gu_ParentCalls1.source034 D hash (s04 s) 5#usize 800#usize 45964#u32 4#usize (by decide)
  have v05 : JGm_TX2_View.View (s05 s) indices05 values05 800 := by
    have v := JGm_TX2_View.after (s04 s) indices04 values04 768 v04
      45964#u32 4#usize (encodeState value034) 800#usize (by decide)
    exact v
  have ri05 : Array.index_usize (s05 s).idx 5#usize=ok 48079#u32 :=
    JGm_TX2_View.index (s05 s) indices05 values05 800 v05 5#usize (by decide)
  have rv05 : Array.index_usize (s05 s).val 5#usize=ok (encodeState value025) :=
    JGm_TX2_View.value (s05 s) indices05 values05 800 v05 5#usize (by decide)
  have active05 : 5#usize<(s05 s).n := by
    change (5:Nat)<(s05 s).n.val
    rw [v05.size]
    decide
  have cursor05 : (s05 s).«at»=800#usize := UScalar.eq_of_val_eq v05.at_eq
  have unpaired05 : ∀ more : 6#usize<(s05 s).n,
      ∃ other,Array.index_usize (s05 s).idx 6#usize=ok other ∧ other≠48079#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨48273#u32,JGm_TX2_View.index (s05 s) indices05 values05 800 v05 6#usize (by decide),by decide⟩
  have read05 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s05 s).«at» 832#usize)=ok (encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])) := by
    rw [cursor05]
    exact read05
  have selected05 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s)
    JGy_G_JGu_Supplied.nodes1 5#usize 5#usize 6#usize 832#usize 3616#usize
    48079#u32 (encodeState value025) (encodeState (JGc_TX2_HashBytes.state [16,128,131,147,46,155,13,197,29,34,144,51,143,28,229,54,178,32,183,183,140,105,113,160,115,195,214,144,94,12,128,80])) ri05 rv05
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired05
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor05];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor05];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor05];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read05
  simp only [show 48079#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected05
  have row05 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize=
        ok (.Next (s06 s) 6#usize 6#usize) := by
    rw [selected05]
    exact JHh_C_Gu_ParentCalls1.source035 D hash (s05 s) 6#usize 832#usize 48079#u32 5#usize (by decide)
  have v06 : JGm_TX2_View.View (s06 s) indices06 values06 832 := by
    have v := JGm_TX2_View.after (s05 s) indices05 values05 800 v05
      48079#u32 5#usize (encodeState value035) 832#usize (by decide)
    exact v
  have ri06 : Array.index_usize (s06 s).idx 6#usize=ok 48273#u32 :=
    JGm_TX2_View.index (s06 s) indices06 values06 832 v06 6#usize (by decide)
  have rv06 : Array.index_usize (s06 s).val 6#usize=ok (encodeState value026) :=
    JGm_TX2_View.value (s06 s) indices06 values06 832 v06 6#usize (by decide)
  have active06 : 6#usize<(s06 s).n := by
    change (6:Nat)<(s06 s).n.val
    rw [v06.size]
    decide
  have cursor06 : (s06 s).«at»=832#usize := UScalar.eq_of_val_eq v06.at_eq
  have unpaired06 : ∀ more : 7#usize<(s06 s).n,
      ∃ other,Array.index_usize (s06 s).idx 7#usize=ok other ∧ other≠48273#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨52342#u32,JGm_TX2_View.index (s06 s) indices06 values06 832 v06 7#usize (by decide),by decide⟩
  have read06 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s06 s).«at» 864#usize)=ok (encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])) := by
    rw [cursor06]
    exact read06
  have selected06 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s)
    JGy_G_JGu_Supplied.nodes1 6#usize 6#usize 7#usize 864#usize 3584#usize
    48273#u32 (encodeState value026) (encodeState (JGc_TX2_HashBytes.state [140,101,31,60,165,201,60,75,58,216,73,119,83,95,32,127,113,252,104,199,28,200,24,47,1,108,50,255,0,221,161,140])) ri06 rv06
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired06
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor06];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor06];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor06];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read06
  simp only [show 48273#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected06
  have row06 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize=
        ok (.Next (s07 s) 7#usize 7#usize) := by
    rw [selected06]
    exact JHh_C_Gu_ParentCalls1.source036 D hash (s06 s) 7#usize 864#usize 48273#u32 6#usize (by decide)
  have v07 : JGm_TX2_View.View (s07 s) indices07 values07 864 := by
    have v := JGm_TX2_View.after (s06 s) indices06 values06 832 v06
      48273#u32 6#usize (encodeState value036) 864#usize (by decide)
    exact v
  have ri07 : Array.index_usize (s07 s).idx 7#usize=ok 52342#u32 :=
    JGm_TX2_View.index (s07 s) indices07 values07 864 v07 7#usize (by decide)
  have rv07 : Array.index_usize (s07 s).val 7#usize=ok (encodeState value027) :=
    JGm_TX2_View.value (s07 s) indices07 values07 864 v07 7#usize (by decide)
  have active07 : 7#usize<(s07 s).n := by
    change (7:Nat)<(s07 s).n.val
    rw [v07.size]
    decide
  have cursor07 : (s07 s).«at»=864#usize := UScalar.eq_of_val_eq v07.at_eq
  have unpaired07 : ∀ more : 8#usize<(s07 s).n,
      ∃ other,Array.index_usize (s07 s).idx 8#usize=ok other ∧ other≠52342#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨54205#u32,JGm_TX2_View.index (s07 s) indices07 values07 864 v07 8#usize (by decide),by decide⟩
  have read07 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s07 s).«at» 896#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])) := by
    rw [cursor07]
    exact read07
  have selected07 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s)
    JGy_G_JGu_Supplied.nodes1 7#usize 7#usize 8#usize 896#usize 3552#usize
    52342#u32 (encodeState value027) (encodeState (JGc_TX2_HashBytes.state [43,150,240,241,176,44,116,229,80,221,23,5,12,189,27,226,164,73,153,251,188,47,181,148,5,149,67,154,125,10,233,211])) ri07 rv07
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired07
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor07];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor07];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor07];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read07
  simp only [show 52342#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected07
  have row07 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize=
        ok (.Next (s08 s) 8#usize 8#usize) := by
    rw [selected07]
    exact JHh_C_Gu_ParentCalls1.source037 D hash (s07 s) 8#usize 896#usize 52342#u32 7#usize (by decide)
  have v08 : JGm_TX2_View.View (s08 s) indices08 values08 896 := by
    have v := JGm_TX2_View.after (s07 s) indices07 values07 864 v07
      52342#u32 7#usize (encodeState value037) 896#usize (by decide)
    exact v
  have ri08 : Array.index_usize (s08 s).idx 8#usize=ok 54205#u32 :=
    JGm_TX2_View.index (s08 s) indices08 values08 896 v08 8#usize (by decide)
  have rv08 : Array.index_usize (s08 s).val 8#usize=ok (encodeState value028) :=
    JGm_TX2_View.value (s08 s) indices08 values08 896 v08 8#usize (by decide)
  have active08 : 8#usize<(s08 s).n := by
    change (8:Nat)<(s08 s).n.val
    rw [v08.size]
    decide
  have cursor08 : (s08 s).«at»=896#usize := UScalar.eq_of_val_eq v08.at_eq
  have unpaired08 : ∀ more : 9#usize<(s08 s).n,
      ∃ other,Array.index_usize (s08 s).idx 9#usize=ok other ∧ other≠54205#u32 ^^^ 1#u32 := by
    intro _
    exact ⟨61474#u32,JGm_TX2_View.index (s08 s) indices08 values08 896 v08 9#usize (by decide),by decide⟩
  have read08 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s08 s).«at» 928#usize)=ok (encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])) := by
    rw [cursor08]
    exact read08
  have selected08 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s)
    JGy_G_JGu_Supplied.nodes1 8#usize 8#usize 9#usize 928#usize 3520#usize
    54205#u32 (encodeState value028) (encodeState (JGc_TX2_HashBytes.state [43,146,168,238,162,23,68,80,31,163,96,208,148,23,64,85,154,125,92,177,215,158,253,133,121,24,22,161,219,238,202,61])) ri08 rv08
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired08
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor08];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor08];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor08];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read08
  simp only [show 54205#u32 &&& 1#u32=1#u32 from rfl,if_neg (by decide : 1#u32≠0#u32)] at selected08
  have row08 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize=
        ok (.Next (s09 s) 9#usize 9#usize) := by
    rw [selected08]
    exact JHh_C_Gu_ParentCalls1.source038 D hash (s08 s) 9#usize 928#usize 54205#u32 8#usize (by decide)
  have v09 : JGm_TX2_View.View (s09 s) indices09 values09 928 := by
    have v := JGm_TX2_View.after (s08 s) indices08 values08 896 v08
      54205#u32 8#usize (encodeState value038) 928#usize (by decide)
    exact v
  have ri09 : Array.index_usize (s09 s).idx 9#usize=ok 61474#u32 :=
    JGm_TX2_View.index (s09 s) indices09 values09 928 v09 9#usize (by decide)
  have rv09 : Array.index_usize (s09 s).val 9#usize=ok (encodeState value029) :=
    JGm_TX2_View.value (s09 s) indices09 values09 928 v09 9#usize (by decide)
  have active09 : 9#usize<(s09 s).n := by
    change (9:Nat)<(s09 s).n.val
    rw [v09.size]
    decide
  have cursor09 : (s09 s).«at»=928#usize := UScalar.eq_of_val_eq v09.at_eq
  have unpaired09 : ∀ more : 10#usize<(s09 s).n,
      ∃ other,Array.index_usize (s09 s).idx 10#usize=ok other ∧ other≠61474#u32 ^^^ 1#u32 := by
    intro more
    change (10:Nat)<(s09 s).n.val at more
    rw [v09.size] at more
    exact False.elim ((by decide : ¬(10:Nat)<10) more)
  have read09 : reference.read32 (MultiproofConeSlices.sub JGy_G_JGu_Supplied.nodes1
      (s09 s).«at» 960#usize)=ok (encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])) := by
    rw [cursor09]
    exact read09
  have selected09 := JGy_G_JGm_TX2_ExternalRun.source
    (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s)
    JGy_G_JGu_Supplied.nodes1 9#usize 9#usize 10#usize 960#usize 3488#usize
    61474#u32 (encodeState value029) (encodeState (JGc_TX2_HashBytes.state [254,103,22,216,177,229,178,69,230,133,92,137,126,145,115,176,102,124,84,213,140,225,194,132,77,135,97,138,229,59,250,215])) ri09 rv09
    (JGy_G_JGm_TX2_Scalar.add _ _ _ rfl) unpaired09
    (by have len : Slice.len JGy_G_JGu_Supplied.nodes1=4416#usize := UScalar.eq_of_val_eq JGy_G_JGu_Supplied.length1
        rw [len,cursor09];exact JGy_G_JGm_TX2_Scalar.sub _ _ _ (by decide) rfl)
    (by decide)
    (by rw [cursor09];exact JGy_G_JGm_TX2_Scalar.add _ _ _ rfl)
    (by rw [cursor09];decide)
    (by rw [JGy_G_JGu_Supplied.length1];decide) read09
  simp only [show 61474#u32 &&& 1#u32=0#u32 from rfl,if_pos rfl] at selected09
  have row09 : reference.binary_step (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash
      (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize=
        ok (.Next (s10 s) 10#usize 10#usize) := by
    rw [selected09]
    exact JHh_C_Gu_ParentCalls1.source039 D hash (s09 s) 10#usize 960#usize 61474#u32 9#usize (by decide)
  have v10 : JGm_TX2_View.View (s10 s) indices10 values10 960 := by
    have v := JGm_TX2_View.after (s09 s) indices09 values09 928 v09
      61474#u32 9#usize (encodeState value039) 960#usize (by decide)
    exact v
  constructor
  · calc
      reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s00 s) JGy_G_JGu_Supplied.nodes1 0#usize 0#usize = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s01 s) JGy_G_JGu_Supplied.nodes1 1#usize 1#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active00 row00
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s02 s) JGy_G_JGu_Supplied.nodes1 2#usize 2#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active01 row01
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s03 s) JGy_G_JGu_Supplied.nodes1 3#usize 3#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active02 row02
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s04 s) JGy_G_JGu_Supplied.nodes1 4#usize 4#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active03 row03
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s05 s) JGy_G_JGu_Supplied.nodes1 5#usize 5#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active04 row04
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s06 s) JGy_G_JGu_Supplied.nodes1 6#usize 6#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active05 row05
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s07 s) JGy_G_JGu_Supplied.nodes1 7#usize 7#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active06 row06
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s08 s) JGy_G_JGu_Supplied.nodes1 8#usize 8#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active07 row07
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s09 s) JGy_G_JGu_Supplied.nodes1 9#usize 9#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active08 row08
      _ = reference.level_rows (Port4B_VerifyInstall.digest (JGy_G_JGc_TX2_RealLeaves.dictionary D)) hash (s10 s) JGy_G_JGu_Supplied.nodes1 10#usize 10#usize :=
        JGy_G_JGm_TX2_RowControl.step _ _ _ _ _ _ _ _ _ active09 row09
      _ = ok (.Done (output s)) := JGy_G_JGm_TX2_RowControl.done _ _ _ _ _ _ (by
        change (s10 s).n.val≤10;rw [v10.size];decide)
  · exact JGm_TX2_View.finish (s10 s) indices10 values10 960
      v10 10#usize (by decide)
#print axioms source
end AspisR1.JHh_C_Gu_Level1_02
end


end
