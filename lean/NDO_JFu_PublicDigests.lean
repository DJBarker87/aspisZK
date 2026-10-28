import NDO_JFu_PublicDigest00
import NDO_JFu_PublicDigest01
import NDO_JFu_PublicDigest02
import NDO_JFu_PublicDigest03
import NDO_JFu_PublicDigest04
import NDO_JFu_PublicDigest05
import NDO_JFu_PublicDigest06
import NDO_JFu_PublicDigest07
import NDO_JFu_PublicDigest08
import NDO_JFu_PublicDigest09
import NDO_JFu_PublicDigest10
import NDO_JFu_PublicDigest11
import NDO_JFu_PublicDigest12
import NDO_JFu_PublicDigest13
import NDO_JFu_PublicDigest14
import NDO_JFu_PublicDigest15
import NDO_JFu_PublicDigest16
import NDO_JFu_PublicDigest17
import NDO_JFu_PublicDigest18
import NDO_JFu_PublicDigest19
import NDO_JFu_PublicDigest20
import NDO_JFu_PublicDigest21
import NDO_JFu_PublicDigest22
import NDO_JFu_PublicDigest23
import NDO_JFu_PublicDigest24
import NDO_JFu_PublicDigest25
import NDO_JFu_PublicDigest26
import NDO_JFu_PublicDigest27
import NDO_JFu_PublicDigest28
import NDO_JFu_PublicDigest29
import NDO_JFu_PublicDigest30
import NDO_JFu_PublicDigest31
import NDO_JFu_PublicDigest32
import NDO_JFu_PublicDigest33
import NDO_JFu_PublicDigest34
import NDO_JFu_PublicDigest35
import NDO_JFu_PublicDigest36
import NDO_JFu_PublicDigest37
import NDO_JFu_PublicDigest38
import NDO_JFu_PublicDigest39
import NDO_JFu_PublicDigest40
import NDO_JFu_PublicDigest41
import NDO_JFu_PublicDigest42
import NDO_JFu_PublicDigest43
import NDO_JFu_PublicDigest44
import NDO_JFu_PublicDigest45
import NDO_JFu_PublicDigest46
set_option autoImplicit false
namespace AspisR1.JFu_PublicDigests
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

def offsets : List Nat := [112, 304, 336, 368, 400, 432, 464, 496, 528, 560, 592, 624, 656, 688, 720, 752, 784, 816, 848, 880, 912, 944, 992, 1024, 1056, 1088, 1120, 1152, 1184, 1216, 1248, 1280, 1312, 1344, 1376, 1408, 1440, 1472, 1504, 1536, 1568, 1600, 1632, 1744, 1776, 1816, 1848]

/-- Every actual semantic digest window of retained public1880 is canonical. -/
theorem canonical_windows : ∀ off ∈ offsets,
    canonical (bytesOf ((JFx_NativeBytes.publicInput.val.drop off).take 32)) := by
  intro off member
  simp only [offsets,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46
  · subst off;rw [JFu_PublicDigest00.selected];exact JFu_PublicDigest00.canonical_bytes
  · subst off;rw [JFu_PublicDigest01.selected];exact JFu_PublicDigest01.canonical_bytes
  · subst off;rw [JFu_PublicDigest02.selected];exact JFu_PublicDigest02.canonical_bytes
  · subst off;rw [JFu_PublicDigest03.selected];exact JFu_PublicDigest03.canonical_bytes
  · subst off;rw [JFu_PublicDigest04.selected];exact JFu_PublicDigest04.canonical_bytes
  · subst off;rw [JFu_PublicDigest05.selected];exact JFu_PublicDigest05.canonical_bytes
  · subst off;rw [JFu_PublicDigest06.selected];exact JFu_PublicDigest06.canonical_bytes
  · subst off;rw [JFu_PublicDigest07.selected];exact JFu_PublicDigest07.canonical_bytes
  · subst off;rw [JFu_PublicDigest08.selected];exact JFu_PublicDigest08.canonical_bytes
  · subst off;rw [JFu_PublicDigest09.selected];exact JFu_PublicDigest09.canonical_bytes
  · subst off;rw [JFu_PublicDigest10.selected];exact JFu_PublicDigest10.canonical_bytes
  · subst off;rw [JFu_PublicDigest11.selected];exact JFu_PublicDigest11.canonical_bytes
  · subst off;rw [JFu_PublicDigest12.selected];exact JFu_PublicDigest12.canonical_bytes
  · subst off;rw [JFu_PublicDigest13.selected];exact JFu_PublicDigest13.canonical_bytes
  · subst off;rw [JFu_PublicDigest14.selected];exact JFu_PublicDigest14.canonical_bytes
  · subst off;rw [JFu_PublicDigest15.selected];exact JFu_PublicDigest15.canonical_bytes
  · subst off;rw [JFu_PublicDigest16.selected];exact JFu_PublicDigest16.canonical_bytes
  · subst off;rw [JFu_PublicDigest17.selected];exact JFu_PublicDigest17.canonical_bytes
  · subst off;rw [JFu_PublicDigest18.selected];exact JFu_PublicDigest18.canonical_bytes
  · subst off;rw [JFu_PublicDigest19.selected];exact JFu_PublicDigest19.canonical_bytes
  · subst off;rw [JFu_PublicDigest20.selected];exact JFu_PublicDigest20.canonical_bytes
  · subst off;rw [JFu_PublicDigest21.selected];exact JFu_PublicDigest21.canonical_bytes
  · subst off;rw [JFu_PublicDigest22.selected];exact JFu_PublicDigest22.canonical_bytes
  · subst off;rw [JFu_PublicDigest23.selected];exact JFu_PublicDigest23.canonical_bytes
  · subst off;rw [JFu_PublicDigest24.selected];exact JFu_PublicDigest24.canonical_bytes
  · subst off;rw [JFu_PublicDigest25.selected];exact JFu_PublicDigest25.canonical_bytes
  · subst off;rw [JFu_PublicDigest26.selected];exact JFu_PublicDigest26.canonical_bytes
  · subst off;rw [JFu_PublicDigest27.selected];exact JFu_PublicDigest27.canonical_bytes
  · subst off;rw [JFu_PublicDigest28.selected];exact JFu_PublicDigest28.canonical_bytes
  · subst off;rw [JFu_PublicDigest29.selected];exact JFu_PublicDigest29.canonical_bytes
  · subst off;rw [JFu_PublicDigest30.selected];exact JFu_PublicDigest30.canonical_bytes
  · subst off;rw [JFu_PublicDigest31.selected];exact JFu_PublicDigest31.canonical_bytes
  · subst off;rw [JFu_PublicDigest32.selected];exact JFu_PublicDigest32.canonical_bytes
  · subst off;rw [JFu_PublicDigest33.selected];exact JFu_PublicDigest33.canonical_bytes
  · subst off;rw [JFu_PublicDigest34.selected];exact JFu_PublicDigest34.canonical_bytes
  · subst off;rw [JFu_PublicDigest35.selected];exact JFu_PublicDigest35.canonical_bytes
  · subst off;rw [JFu_PublicDigest36.selected];exact JFu_PublicDigest36.canonical_bytes
  · subst off;rw [JFu_PublicDigest37.selected];exact JFu_PublicDigest37.canonical_bytes
  · subst off;rw [JFu_PublicDigest38.selected];exact JFu_PublicDigest38.canonical_bytes
  · subst off;rw [JFu_PublicDigest39.selected];exact JFu_PublicDigest39.canonical_bytes
  · subst off;rw [JFu_PublicDigest40.selected];exact JFu_PublicDigest40.canonical_bytes
  · subst off;rw [JFu_PublicDigest41.selected];exact JFu_PublicDigest41.canonical_bytes
  · subst off;rw [JFu_PublicDigest42.selected];exact JFu_PublicDigest42.canonical_bytes
  · subst off;rw [JFu_PublicDigest43.selected];exact JFu_PublicDigest43.canonical_bytes
  · subst off;rw [JFu_PublicDigest44.selected];exact JFu_PublicDigest44.canonical_bytes
  · subst off;rw [JFu_PublicDigest45.selected];exact JFu_PublicDigest45.canonical_bytes
  · subst off;rw [JFu_PublicDigest46.selected];exact JFu_PublicDigest46.canonical_bytes

/-- Successful emitted calls at every actual public digest window; no native wrapper asserted. -/
theorem inhabited : ∀ off ∈ offsets, ∃ (input : Slice U8), ∃ out,
    input.val=(JFx_NativeBytes.publicInput.val.drop off).take 32 ∧
    AspisS6NativeSnapshotReadDigest.read_digest input=ok (.Ok out) := by
  intro off member
  simp only [offsets,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest00.decoded
    exact ⟨JFu_PublicDigest00.window,out,JFu_PublicDigest00.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest01.decoded
    exact ⟨JFu_PublicDigest01.window,out,JFu_PublicDigest01.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest02.decoded
    exact ⟨JFu_PublicDigest02.window,out,JFu_PublicDigest02.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest03.decoded
    exact ⟨JFu_PublicDigest03.window,out,JFu_PublicDigest03.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest04.decoded
    exact ⟨JFu_PublicDigest04.window,out,JFu_PublicDigest04.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest05.decoded
    exact ⟨JFu_PublicDigest05.window,out,JFu_PublicDigest05.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest06.decoded
    exact ⟨JFu_PublicDigest06.window,out,JFu_PublicDigest06.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest07.decoded
    exact ⟨JFu_PublicDigest07.window,out,JFu_PublicDigest07.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest08.decoded
    exact ⟨JFu_PublicDigest08.window,out,JFu_PublicDigest08.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest09.decoded
    exact ⟨JFu_PublicDigest09.window,out,JFu_PublicDigest09.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest10.decoded
    exact ⟨JFu_PublicDigest10.window,out,JFu_PublicDigest10.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest11.decoded
    exact ⟨JFu_PublicDigest11.window,out,JFu_PublicDigest11.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest12.decoded
    exact ⟨JFu_PublicDigest12.window,out,JFu_PublicDigest12.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest13.decoded
    exact ⟨JFu_PublicDigest13.window,out,JFu_PublicDigest13.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest14.decoded
    exact ⟨JFu_PublicDigest14.window,out,JFu_PublicDigest14.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest15.decoded
    exact ⟨JFu_PublicDigest15.window,out,JFu_PublicDigest15.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest16.decoded
    exact ⟨JFu_PublicDigest16.window,out,JFu_PublicDigest16.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest17.decoded
    exact ⟨JFu_PublicDigest17.window,out,JFu_PublicDigest17.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest18.decoded
    exact ⟨JFu_PublicDigest18.window,out,JFu_PublicDigest18.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest19.decoded
    exact ⟨JFu_PublicDigest19.window,out,JFu_PublicDigest19.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest20.decoded
    exact ⟨JFu_PublicDigest20.window,out,JFu_PublicDigest20.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest21.decoded
    exact ⟨JFu_PublicDigest21.window,out,JFu_PublicDigest21.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest22.decoded
    exact ⟨JFu_PublicDigest22.window,out,JFu_PublicDigest22.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest23.decoded
    exact ⟨JFu_PublicDigest23.window,out,JFu_PublicDigest23.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest24.decoded
    exact ⟨JFu_PublicDigest24.window,out,JFu_PublicDigest24.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest25.decoded
    exact ⟨JFu_PublicDigest25.window,out,JFu_PublicDigest25.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest26.decoded
    exact ⟨JFu_PublicDigest26.window,out,JFu_PublicDigest26.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest27.decoded
    exact ⟨JFu_PublicDigest27.window,out,JFu_PublicDigest27.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest28.decoded
    exact ⟨JFu_PublicDigest28.window,out,JFu_PublicDigest28.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest29.decoded
    exact ⟨JFu_PublicDigest29.window,out,JFu_PublicDigest29.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest30.decoded
    exact ⟨JFu_PublicDigest30.window,out,JFu_PublicDigest30.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest31.decoded
    exact ⟨JFu_PublicDigest31.window,out,JFu_PublicDigest31.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest32.decoded
    exact ⟨JFu_PublicDigest32.window,out,JFu_PublicDigest32.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest33.decoded
    exact ⟨JFu_PublicDigest33.window,out,JFu_PublicDigest33.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest34.decoded
    exact ⟨JFu_PublicDigest34.window,out,JFu_PublicDigest34.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest35.decoded
    exact ⟨JFu_PublicDigest35.window,out,JFu_PublicDigest35.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest36.decoded
    exact ⟨JFu_PublicDigest36.window,out,JFu_PublicDigest36.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest37.decoded
    exact ⟨JFu_PublicDigest37.window,out,JFu_PublicDigest37.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest38.decoded
    exact ⟨JFu_PublicDigest38.window,out,JFu_PublicDigest38.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest39.decoded
    exact ⟨JFu_PublicDigest39.window,out,JFu_PublicDigest39.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest40.decoded
    exact ⟨JFu_PublicDigest40.window,out,JFu_PublicDigest40.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest41.decoded
    exact ⟨JFu_PublicDigest41.window,out,JFu_PublicDigest41.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest42.decoded
    exact ⟨JFu_PublicDigest42.window,out,JFu_PublicDigest42.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest43.decoded
    exact ⟨JFu_PublicDigest43.window,out,JFu_PublicDigest43.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest44.decoded
    exact ⟨JFu_PublicDigest44.window,out,JFu_PublicDigest44.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest45.decoded
    exact ⟨JFu_PublicDigest45.window,out,JFu_PublicDigest45.selected.symm,call⟩
  · subst off;obtain ⟨out,call⟩:=JFu_PublicDigest46.decoded
    exact ⟨JFu_PublicDigest46.window,out,JFu_PublicDigest46.selected.symm,call⟩

#print axioms canonical_windows
#print axioms inhabited
end AspisR1.JFu_PublicDigests
