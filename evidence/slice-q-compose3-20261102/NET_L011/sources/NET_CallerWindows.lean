import NEO_QuadraticTotal
import NEO_ParserCallWindows
set_option autoImplicit false
namespace NET_CallerWindows
open Aeneas Aeneas.Std Result

def offset (slot tail : Nat) (first : Bool) : Nat :=
 if first then slot*120+104 else 480+slot*32+tail*16

theorem window_bound (slot tail : Nat) (first : Bool)
 (s : slot<4) (t : tail<2) : offset slot tail first+16≤608 := by
 cases first <;> simp only [offset,Bool.false_eq_true,if_false,if_true] <;> omega

theorem halves_bound (slot tail half : Nat) (first : Bool)
 (s : slot<4) (t : tail<2) (h : half<2) : offset slot tail first+half*8+8≤608 := by
 have bound:=window_bound slot tail first s t
 omega

/-- The three actual dot-call window families on the same full backing slice.
The independently extracted reference and cohort agree on the whole Option,
including all malformed-word rejection prefixes, without a success premise. -/
theorem quadratic (bytes : Slice U8) (size : bytes.val.length=608)
 (slot tail : Nat) (first : Bool) (s : slot<4) (t : tail<2) :
 ∃ bound : offset slot tail first+16≤bytes.val.length,
 let part:=NEO_FixedWindow.window bytes (offset slot tail first) 16#usize bound
 part.val=(bytes.val.drop (offset slot tail first)).take 16 ∧
 NEO_WindowV2.quadratic part.to_slice=NEO_QuadraticCuts.cohort part.to_slice := by
 have bound : offset slot tail first+16≤bytes.val.length := by
  rw [size];exact window_bound slot tail first s t
 refine ⟨bound,rfl,?_⟩
 apply NEO_QuadraticTotal.result
 change 16≤(NEO_FixedWindow.window bytes (offset slot tail first) 16#usize bound).val.length
 rw [(NEO_FixedWindow.window bytes (offset slot tail first) 16#usize bound).hSize]
 decide

/-- Both CM halves remain subwindows of the very same q allocation. -/
theorem complex (bytes : Slice U8) (size : bytes.val.length=608)
 (slot tail half : Nat) (first : Bool) (s : slot<4) (t : tail<2) (h : half<2) :
 ∃ bound : offset slot tail first+half*8+8≤bytes.val.length,
 let part:=NEO_FixedWindow.window bytes (offset slot tail first+half*8) 8#usize bound
 part.val=(bytes.val.drop (offset slot tail first+half*8)).take 8 ∧
 NEO_WindowV2.complex part.to_slice=NEO_ComplexReference.cohort part.to_slice := by
 have bound : offset slot tail first+half*8+8≤bytes.val.length := by
  rw [size];exact halves_bound slot tail half first s t h
 refine ⟨bound,rfl,?_⟩
 apply NEO_ComplexTotal.result
 change 8≤(NEO_FixedWindow.window bytes (offset slot tail first+half*8) 8#usize bound).val.length
 rw [(NEO_FixedWindow.window bytes (offset slot tail first+half*8) 8#usize bound).hSize]
 decide

#print axioms window_bound
#print axioms halves_bound
#print axioms quadratic
#print axioms complex
end NET_CallerWindows
