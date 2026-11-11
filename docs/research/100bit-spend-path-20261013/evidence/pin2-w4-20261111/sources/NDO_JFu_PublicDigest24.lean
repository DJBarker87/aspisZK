import NDO_JFu_DigestSlice
import JFz_CanonicalAppend
import RPz8_JFx_NativeBytes
set_option autoImplicit false
namespace AspisR1.JFu_PublicDigest24
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [200#u8,30#u8,70#u8,52#u8,243#u8,39#u8,23#u8,26#u8,152#u8,166#u8,82#u8,94#u8,13#u8,218#u8,247#u8,91#u8,220#u8,133#u8,34#u8,53#u8,173#u8,98#u8,242#u8,48#u8,30#u8,39#u8,144#u8,31#u8,198#u8,63#u8,59#u8,2#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (JFx_NativeBytes.publicInput.val.drop 1056).take 32=bytes := by
  change (JFx_DataPublic00.bytes.drop 1056).take 32=bytes
  simp only [JFx_DataPublic00.bytes,JFx_DataPublic00.c00_length,JFx_DataPublic00.c01_length,JFx_DataPublic00.c02_length,JFx_DataPublic00.c03_length,JFx_DataPublic00.c04_length,JFx_DataPublic00.c05_length,JFx_DataPublic00.c06_length,JFx_DataPublic00.c07_length,JFx_DataPublic00.c08_length,JFx_DataPublic00.c09_length,JFx_DataPublic00.c10_length,JFx_DataPublic00.c11_length,JFx_DataPublic00.c12_length,JFx_DataPublic00.c13_length,JFx_DataPublic00.c14_length,JFx_DataPublic00.c15_length,JFx_DataPublic00.c16_length,JFx_DataPublic00.c17_length,JFx_DataPublic00.c18_length,JFx_DataPublic00.c19_length,JFx_DataPublic00.c20_length,JFx_DataPublic00.c21_length,JFx_DataPublic00.c22_length,JFx_DataPublic00.c23_length,JFx_DataPublic00.c24_length,JFx_DataPublic00.c25_length,JFx_DataPublic00.c26_length,JFx_DataPublic00.c27_length,JFx_DataPublic00.c28_length,JFx_DataPublic00.c29_length,JFx_DataPublic00.c30_length,JFx_DataPublic00.c31_length,JFx_DataPublic00.c32_length,JFx_DataPublic00.c33_length,JFx_DataPublic00.c34_length,JFx_DataPublic00.c35_length,JFx_DataPublic00.c36_length,JFx_DataPublic00.c37_length,JFx_DataPublic00.c38_length,JFx_DataPublic00.c39_length,JFx_DataPublic00.c40_length,JFx_DataPublic00.c41_length,JFx_DataPublic00.c42_length,JFx_DataPublic00.c43_length,JFx_DataPublic00.c44_length,JFx_DataPublic00.c45_length,JFx_DataPublic00.c46_length,JFx_DataPublic00.c47_length,JFx_DataPublic00.c48_length,JFx_DataPublic00.c49_length,JFx_DataPublic00.c50_length,JFx_DataPublic00.c51_length,JFx_DataPublic00.c52_length,JFx_DataPublic00.c53_length,JFx_DataPublic00.c54_length,JFx_DataPublic00.c55_length,JFx_DataPublic00.c56_length,JFx_DataPublic00.c57_length,JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [200,30,70,52,243,39,23,26,152,166,82,94,13,218,247,91,220,133,34,53,173,98,242,48,30,39,144,31,198,63,59,2]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.JFu_PublicDigest24
