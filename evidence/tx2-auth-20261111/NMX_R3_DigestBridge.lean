import NMX_R3_DigestTotal
import NMX_R3_DigestCanonical
set_option autoImplicit false
namespace NMX_R3_DigestBridge
open Aeneas Aeneas.Std Result RSL NMX_R3_ByteCarrier NMX_R3_DigestWords

def result (r : core.result.Result (Array U32 8#usize) Unit) : Option Digest :=
 match r with
 | .Ok a => some (a.val.map word)
 | .Err () => none

/-- All Results at the same window: no opaque reply, success hypothesis or
canonicality clause is supplied by the caller. -/
theorem value (b : Slice U8) (s : Usize) (cap : b.val.length ≤ 768)
 (fit : s.val + 32 ≤ b.val.length) :
 ∃ r, NCV_Reference.digest b s = ok r ∧
  result r = TX2_217.decodeDigestCanonical (slice (b.val.map byte) s.val (s.val+32)) := by
 classical
 refine ⟨NMX_R3_DigestTotal.outcome b s.val,
  NMX_R3_DigestTotal.value b s cap fit, ?_⟩
 rw [NMX_R3_DigestCanonical.value]
 unfold NMX_R3_DigestTotal.outcome
 split
 · simp only [result, NMX_R3_DigestCarrier.words_exact]
 · rfl
#print axioms value
end NMX_R3_DigestBridge
