import NEO_WindowRelocation
set_option autoImplicit false
namespace NEO_ParserCallWindows
open Aeneas Aeneas.Std Result

theorem dots_offsets (slot : Nat) (small : slot<4) :
 slot*120+104+16≤608 ∧ 480+slot*32+16≤608 ∧ 480+slot*32+16+16≤608 := by omega

theorem scalar_offset (slot term : Nat) (s : slot<4) (t : term<26) :
 slot*120+term*4+4≤608 := by omega

theorem dots_first (bytes : Slice U8) (len : bytes.val.length=608)
 (slot : Nat) (small : slot<4) :
 (NEO_WindowFrame.segment bytes (slot*120+104) 16 (by rw [len]; exact (dots_offsets slot small).1)).length=16 :=
 NEO_WindowFrame.length _ _ _ _

theorem dots_tail (bytes : Slice U8) (len : bytes.val.length=608)
 (slot tail : Nat) (small : slot<4) (bit : tail<2) :
 ∃ bound : 480+slot*32+tail*16+16≤bytes.val.length,
 (NEO_WindowFrame.segment bytes (480+slot*32+tail*16) 16 bound).length=16 := by
 have h : 480+slot*32+tail*16+16≤bytes.val.length := by rw [len]; omega
 exact ⟨h,NEO_WindowFrame.length _ _ _ h⟩

#print axioms dots_offsets
#print axioms scalar_offset
#print axioms dots_first
#print axioms dots_tail
end NEO_ParserCallWindows
