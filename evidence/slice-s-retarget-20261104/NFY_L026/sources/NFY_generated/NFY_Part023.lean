import Lean
import NFY_Part020
import NFY_Part021
import NFY_Part022
import NFY_Part006

-- BEGIN copied JFu_PublicDigest46: lean/JFu_PublicDigest46.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigest46
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def bytes : List U8 := [35#u8,21#u8,136#u8,6#u8,65#u8,19#u8,78#u8,120#u8,113#u8,38#u8,13#u8,70#u8,250#u8,49#u8,224#u8,32#u8,8#u8,134#u8,48#u8,23#u8,1#u8,83#u8,145#u8,33#u8,35#u8,192#u8,81#u8,85#u8,205#u8,25#u8,236#u8,20#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 1848).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 1848).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem canonical_bytes : canonical (bytesOf bytes) := by
  change canonical [35,21,136,6,65,19,78,120,113,38,13,70,250,49,224,32,8,134,48,23,1,83,145,33,35,192,81,85,205,25,236,20]
  simp only [canonical_four]
  exact ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], ⟨by norm_num [little], NFY_JFz_Canonical.nil⟩⟩⟩⟩⟩⟩⟩⟩

def window : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩

theorem decoded : ∃ out,AspisS6NativeSnapshotReadDigest.read_digest window=ok (.Ok out) :=
  NFY_JFu_DigestSlice.success window length canonical_bytes

#print axioms length
#print axioms selected
#print axioms canonical_bytes
#print axioms decoded
end AspisR1.NFY_JFu_PublicDigest46
-- END copied JFu_PublicDigest46
-- BEGIN copied JFu_PublicDigests: lean/JFu_PublicDigests.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicDigests
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def offsets : List Nat := [112, 304, 336, 368, 400, 432, 464, 496, 528, 560, 592, 624, 656, 688, 720, 752, 784, 816, 848, 880, 912, 944, 992, 1024, 1056, 1088, 1120, 1152, 1184, 1216, 1248, 1280, 1312, 1344, 1376, 1408, 1440, 1472, 1504, 1536, 1568, 1600, 1632, 1744, 1776, 1816, 1848]

/-- Every actual semantic digest window of retained public1880 is canonical. -/
theorem canonical_windows : ∀ off ∈ offsets,
    canonical (bytesOf ((NFY_JFx_NativeBytes.publicInput.val.drop off).take 32)) := by
  intro off member
  simp only [offsets,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46
  · subst off;rw [NFY_JFu_PublicDigest00.selected];exact NFY_JFu_PublicDigest00.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest01.selected];exact NFY_JFu_PublicDigest01.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest02.selected];exact NFY_JFu_PublicDigest02.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest03.selected];exact NFY_JFu_PublicDigest03.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest04.selected];exact NFY_JFu_PublicDigest04.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest05.selected];exact NFY_JFu_PublicDigest05.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest06.selected];exact NFY_JFu_PublicDigest06.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest07.selected];exact NFY_JFu_PublicDigest07.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest08.selected];exact NFY_JFu_PublicDigest08.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest09.selected];exact NFY_JFu_PublicDigest09.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest10.selected];exact NFY_JFu_PublicDigest10.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest11.selected];exact NFY_JFu_PublicDigest11.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest12.selected];exact NFY_JFu_PublicDigest12.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest13.selected];exact NFY_JFu_PublicDigest13.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest14.selected];exact NFY_JFu_PublicDigest14.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest15.selected];exact NFY_JFu_PublicDigest15.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest16.selected];exact NFY_JFu_PublicDigest16.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest17.selected];exact NFY_JFu_PublicDigest17.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest18.selected];exact NFY_JFu_PublicDigest18.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest19.selected];exact NFY_JFu_PublicDigest19.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest20.selected];exact NFY_JFu_PublicDigest20.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest21.selected];exact NFY_JFu_PublicDigest21.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest22.selected];exact NFY_JFu_PublicDigest22.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest23.selected];exact NFY_JFu_PublicDigest23.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest24.selected];exact NFY_JFu_PublicDigest24.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest25.selected];exact NFY_JFu_PublicDigest25.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest26.selected];exact NFY_JFu_PublicDigest26.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest27.selected];exact NFY_JFu_PublicDigest27.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest28.selected];exact NFY_JFu_PublicDigest28.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest29.selected];exact NFY_JFu_PublicDigest29.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest30.selected];exact NFY_JFu_PublicDigest30.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest31.selected];exact NFY_JFu_PublicDigest31.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest32.selected];exact NFY_JFu_PublicDigest32.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest33.selected];exact NFY_JFu_PublicDigest33.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest34.selected];exact NFY_JFu_PublicDigest34.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest35.selected];exact NFY_JFu_PublicDigest35.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest36.selected];exact NFY_JFu_PublicDigest36.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest37.selected];exact NFY_JFu_PublicDigest37.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest38.selected];exact NFY_JFu_PublicDigest38.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest39.selected];exact NFY_JFu_PublicDigest39.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest40.selected];exact NFY_JFu_PublicDigest40.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest41.selected];exact NFY_JFu_PublicDigest41.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest42.selected];exact NFY_JFu_PublicDigest42.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest43.selected];exact NFY_JFu_PublicDigest43.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest44.selected];exact NFY_JFu_PublicDigest44.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest45.selected];exact NFY_JFu_PublicDigest45.canonical_bytes
  · subst off;rw [NFY_JFu_PublicDigest46.selected];exact NFY_JFu_PublicDigest46.canonical_bytes

/-- Successful emitted calls at every actual public digest window; no native wrapper asserted. -/
theorem inhabited : ∀ off ∈ offsets, ∃ (input : Slice U8), ∃ out,
    input.val=(NFY_JFx_NativeBytes.publicInput.val.drop off).take 32 ∧
    AspisS6NativeSnapshotReadDigest.read_digest input=ok (.Ok out) := by
  intro off member
  simp only [offsets,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest00.decoded
    exact ⟨NFY_JFu_PublicDigest00.window,out,NFY_JFu_PublicDigest00.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest01.decoded
    exact ⟨NFY_JFu_PublicDigest01.window,out,NFY_JFu_PublicDigest01.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest02.decoded
    exact ⟨NFY_JFu_PublicDigest02.window,out,NFY_JFu_PublicDigest02.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest03.decoded
    exact ⟨NFY_JFu_PublicDigest03.window,out,NFY_JFu_PublicDigest03.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest04.decoded
    exact ⟨NFY_JFu_PublicDigest04.window,out,NFY_JFu_PublicDigest04.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest05.decoded
    exact ⟨NFY_JFu_PublicDigest05.window,out,NFY_JFu_PublicDigest05.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest06.decoded
    exact ⟨NFY_JFu_PublicDigest06.window,out,NFY_JFu_PublicDigest06.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest07.decoded
    exact ⟨NFY_JFu_PublicDigest07.window,out,NFY_JFu_PublicDigest07.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest08.decoded
    exact ⟨NFY_JFu_PublicDigest08.window,out,NFY_JFu_PublicDigest08.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest09.decoded
    exact ⟨NFY_JFu_PublicDigest09.window,out,NFY_JFu_PublicDigest09.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest10.decoded
    exact ⟨NFY_JFu_PublicDigest10.window,out,NFY_JFu_PublicDigest10.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest11.decoded
    exact ⟨NFY_JFu_PublicDigest11.window,out,NFY_JFu_PublicDigest11.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest12.decoded
    exact ⟨NFY_JFu_PublicDigest12.window,out,NFY_JFu_PublicDigest12.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest13.decoded
    exact ⟨NFY_JFu_PublicDigest13.window,out,NFY_JFu_PublicDigest13.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest14.decoded
    exact ⟨NFY_JFu_PublicDigest14.window,out,NFY_JFu_PublicDigest14.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest15.decoded
    exact ⟨NFY_JFu_PublicDigest15.window,out,NFY_JFu_PublicDigest15.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest16.decoded
    exact ⟨NFY_JFu_PublicDigest16.window,out,NFY_JFu_PublicDigest16.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest17.decoded
    exact ⟨NFY_JFu_PublicDigest17.window,out,NFY_JFu_PublicDigest17.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest18.decoded
    exact ⟨NFY_JFu_PublicDigest18.window,out,NFY_JFu_PublicDigest18.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest19.decoded
    exact ⟨NFY_JFu_PublicDigest19.window,out,NFY_JFu_PublicDigest19.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest20.decoded
    exact ⟨NFY_JFu_PublicDigest20.window,out,NFY_JFu_PublicDigest20.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest21.decoded
    exact ⟨NFY_JFu_PublicDigest21.window,out,NFY_JFu_PublicDigest21.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest22.decoded
    exact ⟨NFY_JFu_PublicDigest22.window,out,NFY_JFu_PublicDigest22.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest23.decoded
    exact ⟨NFY_JFu_PublicDigest23.window,out,NFY_JFu_PublicDigest23.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest24.decoded
    exact ⟨NFY_JFu_PublicDigest24.window,out,NFY_JFu_PublicDigest24.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest25.decoded
    exact ⟨NFY_JFu_PublicDigest25.window,out,NFY_JFu_PublicDigest25.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest26.decoded
    exact ⟨NFY_JFu_PublicDigest26.window,out,NFY_JFu_PublicDigest26.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest27.decoded
    exact ⟨NFY_JFu_PublicDigest27.window,out,NFY_JFu_PublicDigest27.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest28.decoded
    exact ⟨NFY_JFu_PublicDigest28.window,out,NFY_JFu_PublicDigest28.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest29.decoded
    exact ⟨NFY_JFu_PublicDigest29.window,out,NFY_JFu_PublicDigest29.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest30.decoded
    exact ⟨NFY_JFu_PublicDigest30.window,out,NFY_JFu_PublicDigest30.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest31.decoded
    exact ⟨NFY_JFu_PublicDigest31.window,out,NFY_JFu_PublicDigest31.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest32.decoded
    exact ⟨NFY_JFu_PublicDigest32.window,out,NFY_JFu_PublicDigest32.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest33.decoded
    exact ⟨NFY_JFu_PublicDigest33.window,out,NFY_JFu_PublicDigest33.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest34.decoded
    exact ⟨NFY_JFu_PublicDigest34.window,out,NFY_JFu_PublicDigest34.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest35.decoded
    exact ⟨NFY_JFu_PublicDigest35.window,out,NFY_JFu_PublicDigest35.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest36.decoded
    exact ⟨NFY_JFu_PublicDigest36.window,out,NFY_JFu_PublicDigest36.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest37.decoded
    exact ⟨NFY_JFu_PublicDigest37.window,out,NFY_JFu_PublicDigest37.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest38.decoded
    exact ⟨NFY_JFu_PublicDigest38.window,out,NFY_JFu_PublicDigest38.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest39.decoded
    exact ⟨NFY_JFu_PublicDigest39.window,out,NFY_JFu_PublicDigest39.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest40.decoded
    exact ⟨NFY_JFu_PublicDigest40.window,out,NFY_JFu_PublicDigest40.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest41.decoded
    exact ⟨NFY_JFu_PublicDigest41.window,out,NFY_JFu_PublicDigest41.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest42.decoded
    exact ⟨NFY_JFu_PublicDigest42.window,out,NFY_JFu_PublicDigest42.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest43.decoded
    exact ⟨NFY_JFu_PublicDigest43.window,out,NFY_JFu_PublicDigest43.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest44.decoded
    exact ⟨NFY_JFu_PublicDigest44.window,out,NFY_JFu_PublicDigest44.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest45.decoded
    exact ⟨NFY_JFu_PublicDigest45.window,out,NFY_JFu_PublicDigest45.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=NFY_JFu_PublicDigest46.decoded
    exact ⟨NFY_JFu_PublicDigest46.window,out,NFY_JFu_PublicDigest46.selected.symm,call⟩

#print axioms canonical_windows
#print axioms inhabited
end AspisR1.NFY_JFu_PublicDigests
-- END copied JFu_PublicDigests
-- BEGIN copied JFu_ResultBranch: lean/JFu_ResultBranch.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_ResultBranch
open Aeneas Aeneas.Std Result

theorem value {T E : Type} (r : core.result.Result T E) (v : T)
    (branch : core.result.Result.Insts.CoreOpsTry.branch r=ok (.Continue v)) : r=.Ok v := by
  cases r <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch]

#print axioms value
end AspisR1.NFY_JFu_ResultBranch
-- END copied JFu_ResultBranch
-- BEGIN copied JFu_DigestCanonical: lean/JFu_DigestCanonical.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestCanonical
open Aeneas Aeneas.Std Result WP
open AspisR1TerminalDecoder

def Canonical (q : Array U32 8#usize) : Prop :=
  ∀ i : Fin 8,(q.val[i.val]'(by simpa only [q.property,show (8#usize).val=8 from rfl] using i.isLt)).val<2147483647

@[local step] theorem word (arr : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes arr
      ⦃ out => ∀ v,out=some v → v.val<2147483647 ⦄ := by
  unfold aspis_core.field.M31.from_le_bytes
  step*
  all_goals intro v same
  all_goals simp_all [aspis_core.field.P]
  all_goals scalar_tac

@[local step] theorem option {T E : Type} (o : Option T) (e : E) :
    core.option.Option.ok_or o e ⦃ out => ∀ v,out=.Ok v → o=some v ⦄ := by
  apply exists_imp_spec
  cases o <;> refine ⟨_,rfl,?_⟩ <;> simp

theorem source (arr : Array U8 32#usize) (out : Array U32 8#usize)
    (accepted : atomic_statement.decode_digest_canonical arr=ok (.Ok out)) : Canonical out := by
  have spec : atomic_statement.decode_digest_canonical arr
      ⦃ result => ∀ q,result=.Ok q → Canonical q ⦄ := by
    unfold atomic_statement.decode_digest_canonical
    step*
    all_goals intro q eq
    all_goals cases eq
    all_goals (have rv0 := NFY_JFu_ResultBranch.value r val (cf_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv0:=o_post _ (r_post _ rv0)
    all_goals (have rv1 := NFY_JFu_ResultBranch.value r1 val1 (cf1_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv1:=o1_post _ (r1_post _ rv1)
    all_goals (have rv2 := NFY_JFu_ResultBranch.value r2 val2 (cf2_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv2:=o2_post _ (r2_post _ rv2)
    all_goals (have rv3 := NFY_JFu_ResultBranch.value r3 val3 (cf3_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv3:=o3_post _ (r3_post _ rv3)
    all_goals (have rv4 := NFY_JFu_ResultBranch.value r4 val4 (cf4_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv4:=o4_post _ (r4_post _ rv4)
    all_goals (have rv5 := NFY_JFu_ResultBranch.value r5 val5 (cf5_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv5:=o5_post _ (r5_post _ rv5)
    all_goals (have rv6 := NFY_JFu_ResultBranch.value r6 val6 (cf6_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv6:=o6_post _ (r6_post _ rv6)
    all_goals (have rv7 := NFY_JFu_ResultBranch.value r7 val7 (cf7_post.trans (congrArg Result.ok (by assumption))))
    all_goals have hv7:=o7_post _ (r7_post _ rv7)
    all_goals unfold Canonical
    all_goals intro j
    all_goals fin_cases j <;> first
      | exact hv0
      | exact hv1
      | exact hv2
      | exact hv3
      | exact hv4
      | exact hv5
      | exact hv6
      | exact hv7
  obtain ⟨result,call,post⟩:=WP.spec_imp_exists spec
  have same : result=.Ok out := Result.ok.inj (call.symm.trans accepted)
  exact post out same

#print axioms word
#print axioms option
#print axioms source
end AspisR1.NFY_JFu_DigestCanonical
-- END copied JFu_DigestCanonical
-- BEGIN copied JFu_DigestSliceCanonical: lean/JFu_DigestSliceCanonical.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestSliceCanonical
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder

theorem source (bytes : Slice U8) (out : Array U32 8#usize)
    (accepted : AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out)) :
    NFY_JFu_DigestCanonical.Canonical out := by
  unfold AspisS6NativeSnapshotReadDigest.read_digest at accepted
  cases cast : core.array.TryFromSharedArraySlice.try_from 32#usize bytes with
  | fail e => simp only [cast,bind_tc_fail] at accepted;cases accepted
  | div => simp only [cast,bind_tc_div] at accepted;cases accepted
  | ok r =>
    cases r with
    | Err e => simp only [cast,bind_tc_ok,atomic_statement.unwrap_fixed_slice,bind_tc_fail] at accepted;cases accepted
    | Ok arr =>
      simp only [cast,bind_tc_ok,atomic_statement.unwrap_fixed_slice] at accepted
      exact NFY_JFu_DigestCanonical.source arr out accepted

#print axioms source
end AspisR1.NFY_JFu_DigestSliceCanonical
-- END copied JFu_DigestSliceCanonical
-- BEGIN copied JFu_DigestSliceFacts: lean/JFu_DigestSliceFacts.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_DigestSliceFacts
open Aeneas Aeneas.Std Result WP
open OraclePortCompactDraft MultiproofConeCanonical

theorem source (bytes : Slice U8) (size : bytes.length=32)
    (canon : canonical (bytesOf bytes.val)) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest bytes=ok (.Ok out) ∧
      NFY_JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=bytes.val := by
  obtain ⟨out,call⟩:=NFY_JFu_DigestSlice.success bytes size canon
  have bound:=NFY_JFu_DigestSliceCanonical.source bytes out call
  obtain ⟨result,read,post⟩:=WP.spec_imp_exists (AspisS6NativeSnapshotReadDigest.read_digest_spec bytes size)
  have same : result=.Ok out := Result.ok.inj (read.symm.trans call)
  exact ⟨out,call,bound,post out same⟩

#print axioms source
end AspisR1.NFY_JFu_DigestSliceFacts
-- END copied JFu_DigestSliceFacts
-- BEGIN copied JFu_PublicWindowFacts: lean/JFu_PublicWindowFacts.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicWindowFacts
open Aeneas Aeneas.Std Result WP
open OraclePortCompactDraft MultiproofConeCanonical

theorem source (off : Nat) (member : off ∈ NFY_JFu_PublicDigests.offsets)
    (input : Slice U8) (same : input.val=(NFY_JFx_NativeBytes.publicInput.val.drop off).take 32)
    (size : input.length=32) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest input=ok (.Ok out) ∧
      NFY_JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=(NFY_JFx_NativeBytes.publicInput.val.drop off).take 32 := by
  have canon : canonical (bytesOf input.val) := by
    rw [same]
    exact NFY_JFu_PublicDigests.canonical_windows off member
  obtain ⟨out,call,bound,contents⟩:=NFY_JFu_DigestSliceFacts.source input size canon
  exact ⟨out,call,bound,contents.trans same⟩

#print axioms source
end AspisR1.NFY_JFu_PublicWindowFacts
-- END copied JFu_PublicWindowFacts
-- BEGIN copied JFt_Range: lean/JFt_Range.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Range
open Aeneas Aeneas.Std Result WP

theorem read (off n : Nat) (bound : off+n≤1880) (start stop : Usize)
    (order : start.val≤stop.val) (inside : stop.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {start:=start,«end»:=stop}=
      ok (NFY_JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega)) := by
  have size:=NFY_JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {start:=start,«end»:=stop}
      ⦃ out => out=NFY_JFu_PublicRange.segment (off+start.val) (stop.val-start.val) (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,NFY_JFu_PublicRange.segment,
      NFY_JFu_PublicRange.nested _ off n start.val (stop.val-start.val) (by omega)] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

theorem digest (off : Nat) (member : off ∈ NFY_JFu_PublicDigests.offsets) (bound : off+32≤1880) :
    ∃ out,AspisS6NativeSnapshotReadDigest.read_digest (NFY_JFu_PublicRange.segment off 32 bound)=ok (.Ok out) ∧
      NFY_JFu_DigestCanonical.Canonical out ∧
      AspisS6SourceCodec.DigestContents.chunks out=(NFY_JFx_NativeBytes.publicInput.val.drop off).take 32 :=
  NFY_JFu_PublicWindowFacts.source off member _ rfl (NFY_JFu_PublicRange.length off 32 bound)

#print axioms read
#print axioms digest
end AspisR1.NFY_JFt_Range
-- END copied JFt_Range
-- BEGIN copied JFt_LocalWindow: lean/JFt_LocalWindow.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_LocalWindow
open Aeneas Aeneas.Std Result WP

theorem selected (off n start count : Nat) (bound : off+start+count≤1880)
    (inside : start+count≤n) (xs : List U8)
    (window : (NFY_JFx_NativeBytes.publicInput.val.drop off).take n=xs) :
    (NFY_JFu_PublicRange.segment (off+start) count bound).val=(xs.drop start).take count := by
  rw [←window]
  exact (NFY_JFu_PublicRange.nested _ off n start count inside).symm

theorem firstn (off n : Nat) (count : Usize) (bound : off+n≤1880) (inside : count.val≤n) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {«end»:=count}=
    ok (NFY_JFu_PublicRange.segment off count.val (by omega)) := by
  have size:=NFY_JFu_PublicRange.length off n bound
  have spec : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      (NFY_JFu_PublicRange.segment off n bound) {«end»:=count}
      ⦃ out => out=NFY_JFu_PublicRange.segment off count.val (by omega) ⦄ := by
    unfold core.slice.index.Slice.index
    step*
    all_goals apply Subtype.ext
    all_goals simpa only [NFY_JFu_PublicRange.segment,List.slice,List.drop_zero,List.take_take,Nat.sub_zero,
      Nat.min_eq_left inside] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms selected
#print axioms firstn
end AspisR1.NFY_JFt_LocalWindow
-- END copied JFt_LocalWindow
-- BEGIN copied JFu_PublicMeta01: lean/JFu_PublicMeta01.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta01
open Aeneas Aeneas.Std Result

def bytes : List U8 := [65#u8,83#u8,80#u8,76#u8,73#u8,86#u8,69#u8,49#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,65#u8,83#u8,80#u8,80#u8,65#u8,73#u8,82#u8,49#u8,1#u8,20#u8,21#u8,7#u8,1#u8,1#u8,1#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=48 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 176).take 48=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 176).take 48=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=176#usize,«end»:=224#usize}=
    ok (NFY_JFu_PublicRange.segment 176 48 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 176#usize 224#usize (by decide) (by decide)
    simpa only [show (176#usize).val=176 from rfl,
      show (224#usize).val=224 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta01
-- END copied JFu_PublicMeta01
-- BEGIN copied JFt_SnapshotHeader: lean/JFt_SnapshotHeader.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotHeader
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def magic : Slice U8 := ⟨NFY_JFu_PublicMeta01.bytes.take 8,by simp [NFY_JFu_PublicMeta01.bytes];scalar_tac⟩
def format : Slice U8 := ⟨(NFY_JFu_PublicMeta01.bytes.drop 16).take 32,by simp [NFY_JFu_PublicMeta01.bytes];scalar_tac⟩

theorem magic_selected : NFY_JFu_PublicRange.segment 176 8 (by decide)=magic := by
  apply Subtype.ext
  exact NFY_JFt_LocalWindow.selected 176 48 0 8 (by decide) (by decide) _ NFY_JFu_PublicMeta01.selected

theorem format_selected : NFY_JFu_PublicRange.segment 192 32 (by decide)=format := by
  apply Subtype.ext
  exact NFY_JFt_LocalWindow.selected 176 48 16 32 (by decide) (by decide) _ NFY_JFu_PublicMeta01.selected

#print pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
#print axioms magic_selected
#print axioms format_selected
end AspisR1.NFY_JFt_SnapshotHeader
-- END copied JFt_SnapshotHeader
-- BEGIN copied JFt_SnapshotConstants: lean/JFt_SnapshotConstants.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_SnapshotConstants
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

def formatArray : Array U8 32#usize :=
  ⟨NFY_JFt_SnapshotHeader.format.val,by simp [NFY_JFt_SnapshotHeader.format,NFY_JFu_PublicMeta01.bytes]⟩

theorem format_call : POOL_V1_PAIR_TREE_FORMAT_BINDING=ok formatArray := by
  obtain ⟨z,add,value⟩:=WP.spec_imp_exists
    (Usize.add_spec (x:=20#usize) (y:=1#usize) (by scalar_tac))
  have same : z=21#usize := by scalar_tac
  rw [same] at add
  unfold POOL_V1_PAIR_TREE_FORMAT_BINDING POOL_V1_PAIR_NOTE_DEPTH
    POOL_V1_PAIR_TREE_DEPTH POOL_V1_PAIR_SECOND_SENTINEL_LANE
    pool_v1.format.POOL_V1_TREE_DEPTH POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION
  have c20 : UScalar.cast .U8 20#usize=20#u8 := by scalar_tac
  have c21 : UScalar.cast .U8 21#usize=21#u8 := by scalar_tac
  have c7 : UScalar.cast .U8 7#usize=7#u8 := by scalar_tac
  simp only [add,lift,bind_tc_ok,c20,c21,c7]
  rfl

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC {start:=0#usize,«end»:=8#usize}=ok NFY_JFt_SnapshotHeader.magic := by
  unfold POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    NFY_JFt_SnapshotHeader.magic NFY_JFt_SnapshotHeader.magic=ok false := by rfl

theorem format_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    formatArray {start:=0#usize,«end»:=32#usize}=ok NFY_JFt_SnapshotHeader.format := by rfl

theorem format_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    NFY_JFt_SnapshotHeader.format NFY_JFt_SnapshotHeader.format=ok false := by rfl

#print axioms format_call
#print axioms magic_array
#print axioms magic_compare
#print axioms format_array
#print axioms format_compare
end AspisR1.NFY_JFt_SnapshotConstants
-- END copied JFt_SnapshotConstants
-- BEGIN copied NBK_LivePrepare: lean/NBK_LivePrepare.lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFY_NBK_LivePrepare
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Snapshot := PoolV1PairLiveSnapshotV1

def run {T : Type} (snapshot : Snapshot) (output : Slice U8)
    (k : LoopStep.Iter → Slice U8 → Result T) : Result T := do
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output { «end» := 8#usize }
      let s1 ← lift (Array.to_slice pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output3 { start := 16#usize, «end» := 48#usize }
      let a ← pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output4 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 48#usize, «end» := 80#usize }
      let s7 ← lift (Array.to_slice snapshot.pool)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output5 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 80#usize, «end» := 112#usize }
      let s10 ← lift (Array.to_slice snapshot.deployment_domain)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output6 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 112#usize, «end» := 120#usize }
      let a1 ← lift (core.num.U64.to_le_bytes snapshot.sequence)
      let s13 ← lift (Array.to_slice a1)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output7 := index_mut_back4 s14
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 120#usize, «end» := 128#usize }
      let a2 ← lift (core.num.U64.to_le_bytes snapshot.next_pair_index)
      let s16 ← lift (Array.to_slice a2)
      let s17 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s15 s16
      let output8 := index_mut_back5 s17
      let (s18, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output8 { start := 128#usize, «end» := 160#usize }
      let a3 ← atomic_statement.encode_digest_canonical snapshot.current_root
      let s19 ← lift (Array.to_slice a3)
      let s20 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s18 s19
      let s21 ← lift (Array.to_slice snapshot.frontier)
      let i1 ← core.slice.Slice.iter s21
      let iter ← core.iter.traits.iterator.Iterator.enumerate.trait_default (core.iter.traits.iterator.IteratorSliceIter (Array aspis_core.field.M31 8#usize)) i1
      let output9 := index_mut_back6 s20
      k iter output9

def value (a : Snapshot) (output : Slice U8) : Slice U8 :=
  ⟨((((((((output.val.setSlice! 0 POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set
      8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION).setSlice!
      16 AspisR1.NFY_JFt_SnapshotConstants.formatArray.val).setSlice!
      48 a.pool.val).setSlice! 80 a.deployment_domain.val).setSlice!
      112 (core.num.U64.to_le_bytes a.sequence).val).setSlice!
      120 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      128 (DigestBytes.bytes a.current_root).val), by
        simpa only [List.length_setSlice!,List.length_set] using output.property⟩

theorem exact {T : Type} (a : Snapshot) (output : Slice U8)
    (size : output.length = 800) (k : LoopStep.Iter → Slice U8 → Result T) :
    run a output k = k (Iterator.cursor a.frontier 0#usize) (value a output) := by
  have len : output.val.length = 800 := size
  unfold run
  simp only [DigestBytes.exact,AspisR1.NFY_JFt_SnapshotConstants.format_call,bind_tc_ok,lift]
  simp [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice, core.slice.Slice.copy_from_slice,
    Slice.length, Slice.len, Slice.update, len, List.slice,
    pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Iterator.cursor,value]

#print axioms exact
end NFY_NBK_LivePrepare
-- END copied NBK_LivePrepare
-- BEGIN copied NBK_Fill: lean/NBK_Fill.lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFY_NBK_Fill

theorem loop (xs acc : List U8) (v : U8) :
    List.mapM.loop (fun _ : U8 => ok v) xs acc =
      ok (acc.reverse ++ List.replicate xs.length v) := by
  induction xs generalizing acc with
  | nil => simp [List.mapM.loop,pure]
  | cons x xs ih => simp [List.mapM.loop,ih,pure,List.reverse_cons,List.replicate_succ,List.append_assoc]

theorem constant (xs : List U8) (v : U8) :
    List.mapM (fun _ => ok v) xs = ok (List.replicate xs.length v) := by
  simpa only [List.mapM,List.reverse_nil,List.nil_append] using loop xs [] v

def value (s : Slice U8) (v : U8) : Slice U8 :=
  ⟨List.replicate s.length v, by simpa only [List.length_replicate,Slice.length] using s.property⟩

theorem source (s : Slice U8) (v : U8) :
    core.slice.Slice.fill core.clone.CloneU8 s v = ok (value s v) := by
  unfold core.slice.Slice.fill
  simp only [core.clone.CloneU8,liftFun1,core.clone.impls.CloneU8.clone,lift]
  split
  next out hm =>
    have fact := constant s.val v
    rw [hm] at fact
    have same := Result.ok.inj fact
    subst out
    rfl
  next e hm =>
    have fact := constant s.val v
    rw [hm] at fact
    cases fact
  next hm =>
    have fact := constant s.val v
    rw [hm] at fact
    cases fact

#print axioms loop
#print axioms constant
#print axioms source
end NFY_NBK_Fill
-- END copied NBK_Fill
-- BEGIN copied NBK_LiveResult: lean/NBK_LiveResult.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBK_LiveResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Snapshot := PoolV1PairLiveSnapshotV1

def zero : Slice U8 := (Array.repeat 800#usize 0#u8).to_slice

def bytes (s : Snapshot) : Slice U8 :=
  NFY_NBK_LiveBytes.fold s.frontier.val 0 (NFY_NBK_LivePrepare.value s zero)

theorem success (s : Snapshot) (output : Slice U8)
    (size : output.length = 800)
    (valid : validate_pool_v1_pair_live_snapshot_v1 s = ok (.Ok ())) :
    encode_pool_v1_pair_live_snapshot_v1 s output = ok (.Ok (),bytes s) := by
  have len : Slice.len output = 800#usize := by scalar_tac
  simp only [encode_pool_v1_pair_live_snapshot_v1,len,
    POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, bne_self_eq_false, if_false,
    valid,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  have fill : core.slice.Slice.fill core.clone.CloneU8 output 0#u8 = ok zero := by
    rw [NFY_NBK_Fill.source]
    congr 1
    apply Subtype.ext
    change List.replicate output.length 0#u8 = List.replicate 800 0#u8
    rw [size]
  rw [fill]
  simp only [bind_tc_ok]
  change NFY_NBK_LivePrepare.run s zero (fun iter out => do
    let encoded ← encode_pool_v1_pair_live_snapshot_v1_loop iter out
    ok (core.result.Result.Ok (),encoded)) = _
  rw [NFY_NBK_LivePrepare.exact s zero (by simp only [zero,Slice.length,Array.to_slice,Array.repeat_val,List.length_replicate]; rfl)]
  have prepared_size : (NFY_NBK_LivePrepare.value s zero).length = 800 := by
    simp only [NFY_NBK_LivePrepare.value,Slice.length,zero,Array.to_slice,Array.repeat_val,List.length_setSlice!,List.length_set,List.length_replicate]
    rfl
  rw [NFY_NBK_LiveBytes.loop_exact s.frontier 0#usize (by decide) _ prepared_size]
  rfl

theorem source (s : Snapshot) (output : Slice U8) :
    encode_pool_v1_pair_live_snapshot_v1 s output =
      if output.length ≠ 800 then ok (.Err .WrongLength,output)
      else match NFY_NBH_LiveValidator.result s with
        | .Ok _ => ok (.Ok (),bytes s)
        | .Err e => ok (.Err e,output) := by
  by_cases size : output.length = 800
  · rw [if_neg (not_not.mpr size)]
    have val := NFY_NBH_LiveValidator.source s
    cases r : NFY_NBH_LiveValidator.result s with
    | Ok u =>
      cases u
      rw [r] at val
      exact success s output size val
    | Err e =>
      rw [r] at val
      have len : Slice.len output = 800#usize := by scalar_tac
      simp only [encode_pool_v1_pair_live_snapshot_v1,len,
        POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, bne_self_eq_false, if_false,
        val,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
      rfl
  · rw [if_pos size]
    have len : Slice.len output ≠ 800#usize := by scalar_tac
    simp only [encode_pool_v1_pair_live_snapshot_v1,
      POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES, ne_eq, bne_iff_ne, len, not_false_eq_true, if_true]

#print axioms success
#print axioms source
end NFY_NBK_LiveResult
-- END copied NBK_LiveResult

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
