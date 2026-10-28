import NDO_JGe_Window27_00
import NDO_JGe_Window27_08
import NDO_JGe_Window27_16
import NDO_JGe_Window27_24
import NDO_JGe_WindowAssembly
import JGe_ValuesAssembly
import NDO_JFw_Y1
set_option autoImplicit false
namespace AspisR1.JGe_Payload27
open Aeneas Aeneas.Std Result
open JGe_Window27
attribute [local irreducible] JFx_NativeBytes.proofBytes
def rawChunks : List (List U8) := [c00,c01,c02,c03,c04,c05,c06,c07,c08,c09,c10,c11,c12,c13,c14,c15,c16,c17,c18,c19,c20,c21,c22,c23,c24,c25,c26,c27,c28]
theorem retained : (JFw_Frames.window 7031 464).val=rawChunks.flatten := by
  have h := JGe_WindowAssembly.source 16 29 7031
  simpa only [JGe_WindowAssembly.chunks,Nat.reduceAdd,rawChunks,selected00,selected01,selected02,selected03,selected04,selected05,selected06,selected07,selected08,selected09,selected10,selected11,selected12,selected13,selected14,selected15,selected16,selected17,selected18,selected19,selected20,selected21,selected22,selected23,selected24,selected25,selected26,selected27,selected28] using h
#print axioms retained
theorem lengths : ∀ c∈rawChunks,c.length=16 := by
  intro c hc
  simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
  · subst c;rfl
#print axioms lengths
def sourceChunks : List (List U8) := rawChunks.map (fun c => c ++ List.replicate 16 0#u8)
def value : Slice U8 := JFw_Frames.expandedPayload 29 7031 (by decide) (by decide)
theorem bytes : value.val=sourceChunks.flatten := by
  change (JFw_Blocks.blocks 29 (JFw_Frames.window 7031 464).val).flatten=_
  rw [retained]
  exact congrArg List.flatten (JGe_ValuesAssembly.source rawChunks lengths)
#print axioms bytes
theorem source : AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),value) := by
  obtain ⟨out,call,size,hbytes⟩ := JFw_Y1.inhabited
  have expected := JFw_Frames.expanded_bytes 29 7031 (by decide) (by decide)
  have same : out=value := Subtype.ext (MultiproofConeByteEquality.bytes_injective (hbytes.trans expected.symm))
  exact same ▸ call
#print axioms source
theorem length : value.length=928 := JFw_Frames.expanded_length 29 7031 (by decide) (by decide)
#print axioms length
end AspisR1.JGe_Payload27
