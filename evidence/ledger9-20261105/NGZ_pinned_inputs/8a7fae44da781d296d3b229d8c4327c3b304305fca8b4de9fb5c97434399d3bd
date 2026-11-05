import Lean
import Op4P_Refinement
import MultiproofConeCanonicalAppend
import NFY_Part020

-- BEGIN copied JFz_Canonical: lean/JFz_Canonical.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JFz_Canonical
open AspisV8R19.DuplexFrames OraclePortCompactDraft

theorem nil : canonical [] := by
  constructor
  · rfl
  · intro j hj
    simp only [List.length_nil, Nat.zero_div, List.mem_range] at hj
    omega

/-- Four-byte induction; evaluation of each numeral is confined to one word. -/
theorem cons4 (a b c d : Fin 256) (tail : Bytes)
    (word : little [a,b,c,d] < 2147483647) (rest : canonical tail) :
    canonical (a::b::c::d::tail) := by
  rcases rest with ⟨multiple, valid⟩
  constructor
  · simp only [List.length_cons]
    omega
  · intro j hj
    simp only [List.mem_range, List.length_cons] at hj
    cases j with
    | zero => simpa only [Nat.mul_zero, slice, List.drop_zero,
        List.take_succ_cons, List.take_zero] using word
    | succ j =>
      have hj' : j ∈ List.range (tail.length / 4) := by
        simp only [List.mem_range]
        omega
      have h := valid j hj'
      simpa only [slice, Nat.mul_succ, List.drop_succ_cons] using h

#print axioms nil
#print axioms cons4
end AspisR1.NFY_JFz_Canonical
end
-- END copied JFz_Canonical
-- BEGIN copied JFz_CanonicalAppend: lean/JFz_CanonicalAppend.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFz_CanonicalAppend
open Aeneas Aeneas.Std OraclePortCompactDraft MultiproofConeCanonical

theorem join (xs ys : List U8) (hx : canonical (bytesOf xs))
    (hy : canonical (bytesOf ys)) : canonical (bytesOf (xs ++ ys)) := by
  rw [bytesOf,List.map_append]
  exact (MultiproofConeCanonicalAppend.canonical_append _ _ hx.1).mpr ⟨hx,hy⟩

/-- Reassemble adjacent bounded ranges without unfolding byte data. -/
theorem slice_join {α : Type} (xs : List α) (off n m : Nat) :
    (xs.drop off).take (n+m) =
      (xs.drop off).take n ++ (xs.drop (off+n)).take m := by
  rw [← List.take_append_drop n ((xs.drop off).take (n+m))]
  simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right n m),
    List.drop_take, List.drop_drop, Nat.add_sub_cancel_left]

#print axioms join
#print axioms slice_join
end AspisR1.NFY_JFz_CanonicalAppend
-- END copied JFz_CanonicalAppend
-- BEGIN copied JFu_PublicDigest00: lean/JFu_PublicDigest00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest00
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [85#u8,246#u8,62#u8,4#u8,159#u8,80#u8,117#u8,33#u8,221#u8,239#u8,128#u8,120#u8,216#u8,131#u8,141#u8,49#u8,99#u8,239#u8,102#u8,35#u8,253#u8,148#u8,147#u8,6#u8,128#u8,120#u8,67#u8,103#u8,86#u8,177#u8,157#u8,56#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 112).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 112).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [85,246,62,4,159,80,117,33,221,239,128,120,216,131,141,49,99,239,102,35,253,148,147,6,128,120,67,103,86,177,157,56]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest00
-- END copied JFu_PublicDigest00
-- BEGIN copied JFu_PublicDigest01: lean/JFu_PublicDigest01.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest01
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [168#u8,25#u8,21#u8,63#u8,56#u8,87#u8,108#u8,72#u8,238#u8,16#u8,205#u8,42#u8,211#u8,24#u8,246#u8,120#u8,68#u8,197#u8,159#u8,70#u8,239#u8,139#u8,30#u8,125#u8,121#u8,73#u8,141#u8,36#u8,169#u8,71#u8,87#u8,98#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 304).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 304).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [168,25,21,63,56,87,108,72,238,16,205,42,211,24,246,120,68,197,159,70,239,139,30,125,121,73,141,36,169,71,87,98]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest01
-- END copied JFu_PublicDigest01
-- BEGIN copied JFu_PublicDigest02: lean/JFu_PublicDigest02.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest02
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [160#u8,79#u8,0#u8,0#u8,177#u8,79#u8,0#u8,0#u8,194#u8,79#u8,0#u8,0#u8,211#u8,79#u8,0#u8,0#u8,228#u8,79#u8,0#u8,0#u8,245#u8,79#u8,0#u8,0#u8,6#u8,80#u8,0#u8,0#u8,23#u8,80#u8,0#u8,0#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 336).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 336).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [160,79,0,0,177,79,0,0,194,79,0,0,211,79,0,0,228,79,0,0,245,79,0,0,6,80,0,0,23,80,0,0]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest02
-- END copied JFu_PublicDigest02
-- BEGIN copied JFu_PublicDigest03: lean/JFu_PublicDigest03.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest03
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [235#u8,242#u8,112#u8,8#u8,230#u8,167#u8,79#u8,86#u8,213#u8,99#u8,65#u8,31#u8,155#u8,22#u8,230#u8,115#u8,109#u8,214#u8,51#u8,109#u8,67#u8,248#u8,134#u8,34#u8,158#u8,228#u8,215#u8,44#u8,40#u8,233#u8,227#u8,61#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 368).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 368).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [235,242,112,8,230,167,79,86,213,99,65,31,155,22,230,115,109,214,51,109,67,248,134,34,158,228,215,44,40,233,227,61]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest03
-- END copied JFu_PublicDigest03
-- BEGIN copied JFu_PublicDigest04: lean/JFu_PublicDigest04.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest04
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [255#u8,87#u8,97#u8,33#u8,138#u8,206#u8,138#u8,6#u8,157#u8,239#u8,19#u8,123#u8,225#u8,92#u8,150#u8,20#u8,2#u8,84#u8,103#u8,72#u8,62#u8,69#u8,216#u8,21#u8,199#u8,140#u8,96#u8,27#u8,54#u8,40#u8,170#u8,28#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 400).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 400).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [255,87,97,33,138,206,138,6,157,239,19,123,225,92,150,20,2,84,103,72,62,69,216,21,199,140,96,27,54,40,170,28]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest04
-- END copied JFu_PublicDigest04
-- BEGIN copied JFu_PublicDigest05: lean/JFu_PublicDigest05.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest05
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [220#u8,22#u8,145#u8,95#u8,145#u8,152#u8,13#u8,74#u8,123#u8,196#u8,190#u8,68#u8,229#u8,88#u8,119#u8,23#u8,151#u8,91#u8,145#u8,42#u8,200#u8,68#u8,213#u8,124#u8,141#u8,247#u8,83#u8,3#u8,10#u8,128#u8,152#u8,39#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 432).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 432).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [220,22,145,95,145,152,13,74,123,196,190,68,229,88,119,23,151,91,145,42,200,68,213,124,141,247,83,3,10,128,152,39]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest05
-- END copied JFu_PublicDigest05
-- BEGIN copied JFu_PublicDigest06: lean/JFu_PublicDigest06.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest06
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [62#u8,185#u8,11#u8,84#u8,185#u8,239#u8,40#u8,40#u8,161#u8,49#u8,20#u8,56#u8,246#u8,242#u8,89#u8,16#u8,87#u8,146#u8,125#u8,102#u8,5#u8,17#u8,194#u8,100#u8,139#u8,155#u8,28#u8,12#u8,232#u8,192#u8,152#u8,110#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 464).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 464).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [62,185,11,84,185,239,40,40,161,49,20,56,246,242,89,16,87,146,125,102,5,17,194,100,139,155,28,12,232,192,152,110]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest06
-- END copied JFu_PublicDigest06
-- BEGIN copied JFu_PublicDigest07: lean/JFu_PublicDigest07.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest07
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [72#u8,196#u8,254#u8,85#u8,234#u8,129#u8,207#u8,91#u8,207#u8,92#u8,67#u8,11#u8,242#u8,147#u8,17#u8,6#u8,34#u8,176#u8,68#u8,112#u8,15#u8,75#u8,197#u8,105#u8,67#u8,238#u8,226#u8,77#u8,176#u8,120#u8,113#u8,33#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 496).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 496).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [72,196,254,85,234,129,207,91,207,92,67,11,242,147,17,6,34,176,68,112,15,75,197,105,67,238,226,77,176,120,113,33]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest07
-- END copied JFu_PublicDigest07
-- BEGIN copied JFu_PublicDigest08: lean/JFu_PublicDigest08.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest08
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [75#u8,25#u8,142#u8,14#u8,189#u8,74#u8,171#u8,58#u8,248#u8,40#u8,123#u8,87#u8,29#u8,243#u8,253#u8,122#u8,132#u8,18#u8,67#u8,105#u8,55#u8,43#u8,137#u8,77#u8,171#u8,212#u8,28#u8,94#u8,67#u8,3#u8,118#u8,44#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 528).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 528).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [75,25,142,14,189,74,171,58,248,40,123,87,29,243,253,122,132,18,67,105,55,43,137,77,171,212,28,94,67,3,118,44]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest08
-- END copied JFu_PublicDigest08
-- BEGIN copied JFu_PublicDigest09: lean/JFu_PublicDigest09.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest09
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [52#u8,27#u8,32#u8,40#u8,28#u8,234#u8,68#u8,2#u8,163#u8,38#u8,163#u8,86#u8,127#u8,150#u8,231#u8,79#u8,106#u8,166#u8,245#u8,21#u8,72#u8,207#u8,86#u8,109#u8,247#u8,208#u8,24#u8,16#u8,151#u8,176#u8,107#u8,42#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 560).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 560).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [52,27,32,40,28,234,68,2,163,38,163,86,127,150,231,79,106,166,245,21,72,207,86,109,247,208,24,16,151,176,107,42]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest09
-- END copied JFu_PublicDigest09
-- BEGIN copied JFu_PublicDigest10: lean/JFu_PublicDigest10.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest10
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [251#u8,100#u8,157#u8,1#u8,108#u8,224#u8,214#u8,75#u8,57#u8,61#u8,127#u8,59#u8,232#u8,158#u8,237#u8,86#u8,69#u8,185#u8,229#u8,52#u8,82#u8,167#u8,210#u8,71#u8,84#u8,131#u8,134#u8,51#u8,14#u8,221#u8,0#u8,33#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 592).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 592).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [251,100,157,1,108,224,214,75,57,61,127,59,232,158,237,86,69,185,229,52,82,167,210,71,84,131,134,51,14,221,0,33]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest10
-- END copied JFu_PublicDigest10
-- BEGIN copied JFu_PublicDigest11: lean/JFu_PublicDigest11.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest11
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [56#u8,88#u8,152#u8,117#u8,59#u8,185#u8,142#u8,73#u8,83#u8,82#u8,62#u8,58#u8,162#u8,134#u8,152#u8,101#u8,189#u8,172#u8,106#u8,96#u8,112#u8,205#u8,110#u8,108#u8,214#u8,96#u8,7#u8,54#u8,101#u8,209#u8,142#u8,98#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 624).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 624).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [56,88,152,117,59,185,142,73,83,82,62,58,162,134,152,101,189,172,106,96,112,205,110,108,214,96,7,54,101,209,142,98]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest11
-- END copied JFu_PublicDigest11
-- BEGIN copied JFu_PublicDigest12: lean/JFu_PublicDigest12.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest12
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [172#u8,172#u8,239#u8,24#u8,212#u8,157#u8,35#u8,28#u8,253#u8,213#u8,245#u8,51#u8,223#u8,50#u8,229#u8,5#u8,168#u8,87#u8,206#u8,120#u8,18#u8,119#u8,176#u8,89#u8,46#u8,133#u8,70#u8,24#u8,221#u8,119#u8,86#u8,107#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 656).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 656).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [172,172,239,24,212,157,35,28,253,213,245,51,223,50,229,5,168,87,206,120,18,119,176,89,46,133,70,24,221,119,86,107]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest12
-- END copied JFu_PublicDigest12
-- BEGIN copied JFu_PublicDigest13: lean/JFu_PublicDigest13.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest13
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [56#u8,89#u8,202#u8,58#u8,185#u8,34#u8,92#u8,39#u8,7#u8,78#u8,84#u8,60#u8,134#u8,220#u8,15#u8,27#u8,200#u8,114#u8,222#u8,58#u8,99#u8,41#u8,32#u8,37#u8,26#u8,85#u8,146#u8,68#u8,78#u8,228#u8,75#u8,76#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 688).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 688).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [56,89,202,58,185,34,92,39,7,78,84,60,134,220,15,27,200,114,222,58,99,41,32,37,26,85,146,68,78,228,75,76]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest13
-- END copied JFu_PublicDigest13
-- BEGIN copied JFu_PublicDigest14: lean/JFu_PublicDigest14.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest14
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [37#u8,76#u8,69#u8,126#u8,125#u8,129#u8,184#u8,101#u8,165#u8,135#u8,222#u8,126#u8,89#u8,61#u8,248#u8,9#u8,14#u8,31#u8,105#u8,24#u8,136#u8,30#u8,222#u8,78#u8,213#u8,153#u8,15#u8,112#u8,216#u8,86#u8,100#u8,122#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 720).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 720).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [37,76,69,126,125,129,184,101,165,135,222,126,89,61,248,9,14,31,105,24,136,30,222,78,213,153,15,112,216,86,100,122]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest14
-- END copied JFu_PublicDigest14
-- BEGIN copied JFu_PublicDigest15: lean/JFu_PublicDigest15.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest15
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [157#u8,161#u8,135#u8,15#u8,109#u8,191#u8,246#u8,81#u8,23#u8,128#u8,109#u8,94#u8,214#u8,254#u8,99#u8,65#u8,176#u8,172#u8,116#u8,100#u8,254#u8,254#u8,213#u8,63#u8,149#u8,255#u8,253#u8,125#u8,238#u8,33#u8,29#u8,57#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 752).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 752).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [157,161,135,15,109,191,246,81,23,128,109,94,214,254,99,65,176,172,116,100,254,254,213,63,149,255,253,125,238,33,29,57]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest15
-- END copied JFu_PublicDigest15
-- BEGIN copied JFu_PublicDigest16: lean/JFu_PublicDigest16.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest16
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [17#u8,99#u8,232#u8,73#u8,51#u8,32#u8,40#u8,59#u8,154#u8,101#u8,76#u8,83#u8,245#u8,164#u8,208#u8,27#u8,117#u8,211#u8,126#u8,123#u8,26#u8,114#u8,127#u8,42#u8,70#u8,166#u8,9#u8,122#u8,215#u8,50#u8,38#u8,100#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 784).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 784).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [17,99,232,73,51,32,40,59,154,101,76,83,245,164,208,27,117,211,126,123,26,114,127,42,70,166,9,122,215,50,38,100]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest16
-- END copied JFu_PublicDigest16
-- BEGIN copied JFu_PublicDigest17: lean/JFu_PublicDigest17.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest17
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [0#u8,105#u8,16#u8,107#u8,224#u8,25#u8,1#u8,111#u8,168#u8,192#u8,126#u8,116#u8,58#u8,110#u8,248#u8,70#u8,121#u8,225#u8,188#u8,21#u8,129#u8,142#u8,204#u8,2#u8,240#u8,239#u8,1#u8,40#u8,149#u8,53#u8,103#u8,72#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 816).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 816).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [0,105,16,107,224,25,1,111,168,192,126,116,58,110,248,70,121,225,188,21,129,142,204,2,240,239,1,40,149,53,103,72]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest17
-- END copied JFu_PublicDigest17
-- BEGIN copied JFu_PublicDigest18: lean/JFu_PublicDigest18.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest18
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [144#u8,141#u8,57#u8,67#u8,64#u8,122#u8,130#u8,39#u8,252#u8,17#u8,2#u8,5#u8,94#u8,184#u8,79#u8,59#u8,43#u8,116#u8,158#u8,84#u8,243#u8,18#u8,51#u8,117#u8,18#u8,243#u8,231#u8,49#u8,249#u8,200#u8,45#u8,124#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 848).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 848).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [144,141,57,67,64,122,130,39,252,17,2,5,94,184,79,59,43,116,158,84,243,18,51,117,18,243,231,49,249,200,45,124]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest18
-- END copied JFu_PublicDigest18
-- BEGIN copied JFu_PublicDigest19: lean/JFu_PublicDigest19.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest19
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [182#u8,57#u8,199#u8,78#u8,108#u8,219#u8,165#u8,46#u8,232#u8,179#u8,99#u8,84#u8,222#u8,207#u8,111#u8,4#u8,217#u8,42#u8,70#u8,46#u8,60#u8,243#u8,66#u8,19#u8,57#u8,207#u8,146#u8,25#u8,125#u8,32#u8,124#u8,77#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 880).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 880).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [182,57,199,78,108,219,165,46,232,179,99,84,222,207,111,4,217,42,70,46,60,243,66,19,57,207,146,25,125,32,124,77]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest19
-- END copied JFu_PublicDigest19
-- BEGIN copied JFu_PublicDigest20: lean/JFu_PublicDigest20.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest20
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [116#u8,183#u8,140#u8,90#u8,100#u8,144#u8,165#u8,73#u8,16#u8,243#u8,160#u8,99#u8,14#u8,89#u8,103#u8,86#u8,213#u8,51#u8,160#u8,32#u8,201#u8,207#u8,159#u8,96#u8,34#u8,247#u8,231#u8,15#u8,83#u8,126#u8,218#u8,26#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 912).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 912).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [116,183,140,90,100,144,165,73,16,243,160,99,14,89,103,86,213,51,160,32,201,207,159,96,34,247,231,15,83,126,218,26]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest20
-- END copied JFu_PublicDigest20
-- BEGIN copied JFu_PublicDigest21: lean/JFu_PublicDigest21.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest21
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [123#u8,190#u8,39#u8,1#u8,217#u8,63#u8,5#u8,78#u8,38#u8,224#u8,4#u8,15#u8,229#u8,231#u8,69#u8,28#u8,172#u8,155#u8,93#u8,123#u8,197#u8,163#u8,23#u8,111#u8,35#u8,173#u8,17#u8,9#u8,211#u8,192#u8,171#u8,39#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 944).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 944).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [123,190,39,1,217,63,5,78,38,224,4,15,229,231,69,28,172,155,93,123,197,163,23,111,35,173,17,9,211,192,171,39]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest21
-- END copied JFu_PublicDigest21

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
