import NDO_JGc_TX2_M2Level17
import RPt_JFo_Prepared
import Port4B_KeyInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_M2Root
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OracleDecisionMultiBuild OracleDecisionMultiTree JGc_TX2_M2Roots

def retainedRoot : State := JGc_TX2_HashBytes.state
  [46,133,21,235,161,197,244,215,120,165,246,0,196,252,96,124,
   6,55,195,101,6,216,73,254,64,84,104,238,161,99,66,102]

theorem selected_queries : OraclePortSelectedDraft.selected
    (Port4B_KeyInstall.queries JFo_Prepared.value.queries) 1 2=indices := rfl
#print axioms selected_queries
def rootBytes : List Aeneas.Std.U8 := [46#u8,133#u8,21#u8,235#u8,161#u8,197#u8,244#u8,215#u8,120#u8,165#u8,246#u8,0#u8,196#u8,252#u8,96#u8,124#u8,6#u8,55#u8,195#u8,101#u8,6#u8,216#u8,73#u8,254#u8,64#u8,84#u8,104#u8,238#u8,161#u8,99#u8,66#u8,102#u8]
theorem selected_root : (JFx_NativeBytes.proof.val.drop 7751).take 32=rootBytes := by
  simp only [JFx_NativeBytes.proof,JFx_NativeBytes.proofBytes,JFx_DataProof00.length,JFx_DataProof01.length,JFx_DataProof02.length,JFx_DataProof03.length,JFx_DataProof04.length,JFx_DataProof05.length,JFx_DataProof06.length,JFx_DataProof07.length,JFx_DataProof08.length,JFx_DataProof09.length,JFx_DataProof10.length,JFx_DataProof11.length,JFx_DataProof12.length,JFx_DataProof13.length,JFx_DataProof14.length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  simp only [JFx_DataProof01.bytes,JFx_DataProof01.c00_length,JFx_DataProof01.c01_length,JFx_DataProof01.c02_length,JFx_DataProof01.c03_length,JFx_DataProof01.c04_length,JFx_DataProof01.c05_length,JFx_DataProof01.c06_length,JFx_DataProof01.c07_length,JFx_DataProof01.c08_length,JFx_DataProof01.c09_length,JFx_DataProof01.c10_length,JFx_DataProof01.c11_length,JFx_DataProof01.c12_length,JFx_DataProof01.c13_length,JFx_DataProof01.c14_length,JFx_DataProof01.c15_length,JFx_DataProof01.c16_length,JFx_DataProof01.c17_length,JFx_DataProof01.c18_length,JFx_DataProof01.c19_length,JFx_DataProof01.c20_length,JFx_DataProof01.c21_length,JFx_DataProof01.c22_length,JFx_DataProof01.c23_length,JFx_DataProof01.c24_length,JFx_DataProof01.c25_length,JFx_DataProof01.c26_length,JFx_DataProof01.c27_length,JFx_DataProof01.c28_length,JFx_DataProof01.c29_length,JFx_DataProof01.c30_length,JFx_DataProof01.c31_length,JFx_DataProof01.c32_length,JFx_DataProof01.c33_length,JFx_DataProof01.c34_length,JFx_DataProof01.c35_length,JFx_DataProof01.c36_length,JFx_DataProof01.c37_length,JFx_DataProof01.c38_length,JFx_DataProof01.c39_length,JFx_DataProof01.c40_length,JFx_DataProof01.c41_length,JFx_DataProof01.c42_length,JFx_DataProof01.c43_length,JFx_DataProof01.c44_length,JFx_DataProof01.c45_length,JFx_DataProof01.c46_length,JFx_DataProof01.c47_length,JFx_DataProof01.c48_length,JFx_DataProof01.c49_length,JFx_DataProof01.c50_length,JFx_DataProof01.c51_length,JFx_DataProof01.c52_length,JFx_DataProof01.c53_length,JFx_DataProof01.c54_length,JFx_DataProof01.c55_length,JFx_DataProof01.c56_length,JFx_DataProof01.c57_length,JFx_DataProof01.c58_length,JFx_DataProof01.c59_length,JFx_DataProof01.c60_length,JFx_DataProof01.c61_length,JFx_DataProof01.c62_length,JFx_DataProof01.c63_length,JFx_DataProof01.c64_length,JFx_DataProof01.c65_length,JFx_DataProof01.c66_length,JFx_DataProof01.c67_length,JFx_DataProof01.c68_length,JFx_DataProof01.c69_length,JFx_DataProof01.c70_length,JFx_DataProof01.c71_length,JFx_DataProof01.c72_length,JFx_DataProof01.c73_length,JFx_DataProof01.c74_length,JFx_DataProof01.c75_length,JFx_DataProof01.c76_length,JFx_DataProof01.c77_length,JFx_DataProof01.c78_length,JFx_DataProof01.c79_length,JFx_DataProof01.c80_length,JFx_DataProof01.c81_length,JFx_DataProof01.c82_length,JFx_DataProof01.c83_length,JFx_DataProof01.c84_length,JFx_DataProof01.c85_length,JFx_DataProof01.c86_length,JFx_DataProof01.c87_length,JFx_DataProof01.c88_length,JFx_DataProof01.c89_length,JFx_DataProof01.c90_length,JFx_DataProof01.c91_length,JFx_DataProof01.c92_length,JFx_DataProof01.c93_length,JFx_DataProof01.c94_length,JFx_DataProof01.c95_length,JFx_DataProof01.c96_length,JFx_DataProof01.c97_length,JFx_DataProof01.c98_length,JFx_DataProof01.c99_length,JFx_DataProof01.c100_length,JFx_DataProof01.c101_length,JFx_DataProof01.c102_length,JFx_DataProof01.c103_length,JFx_DataProof01.c104_length,JFx_DataProof01.c105_length,JFx_DataProof01.c106_length,JFx_DataProof01.c107_length,JFx_DataProof01.c108_length,JFx_DataProof01.c109_length,JFx_DataProof01.c110_length,JFx_DataProof01.c111_length,JFx_DataProof01.c112_length,JFx_DataProof01.c113_length,JFx_DataProof01.c114_length,JFx_DataProof01.c115_length,JFx_DataProof01.c116_length,JFx_DataProof01.c117_length,JFx_DataProof01.c118_length,JFx_DataProof01.c119_length,JFx_DataProof01.c120_length,JFx_DataProof01.c121_length,JFx_DataProof01.c122_length,JFx_DataProof01.c123_length,JFx_DataProof01.c124_length,JFx_DataProof01.c125_length,JFx_DataProof01.c126_length,JFx_DataProof01.c127_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl
#print axioms selected_root
theorem encoded_root : (AspisV8R19.SqueezeOracleBridge.encodeState retainedRoot).val=rootBytes := by rfl
#print axioms encoded_root

theorem value_eq : value163=retainedRoot := by
  funext i
  fin_cases i <;> rfl

theorem source (f : Nat → Bytes) (g : Nat → Nat → State)
    (inputs : InputLaw f) (siblings : SiblingLaw g) :
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot := by
  rw [shape163 f g inputs siblings,root163,value_eq]

theorem inhabited : ∃ (f : Nat → Bytes) (g : Nat → Nat → State),
    InputLaw f ∧ SiblingLaw g ∧
    root JFp_SHADigest.digest (build indices f g 18 0)=retainedRoot :=
  ⟨inputAt,siblingAt,(by intro b _;rfl),(by intro h _ b _;rfl),
    source inputAt siblingAt (by intro b _;rfl) (by intro h _ b _;rfl)⟩
#print axioms value_eq
#print axioms source
#print axioms inhabited
end AspisR1.JGc_TX2_M2Root
end
