import NMX_R3_Word32
set_option autoImplicit false
namespace NMX_R3_WordRead
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier

def valueAt (b : Slice U8) (s : Nat) : UInt32 :=
 RSL.le32 (byte (NCV_ZeroStep.byte b s)) (byte (NCV_ZeroStep.byte b (s+1)))
  (byte (NCV_ZeroStep.byte b (s+2))) (byte (NCV_ZeroStep.byte b (s+3)))

/-- Exact all-input word return at every caller-established in-range window. -/
theorem value (b : Slice U8) (s : Usize) (fit : s.val + 4 ≤ b.val.length) :
 ∃ w : U32, NCV_Reference.word32 b s = ok w ∧ word w = valueAt b s.val := by
 let a : Array U8 4#usize := Array.make 4#usize
  [NCV_ZeroStep.byte b s.val, NCV_ZeroStep.byte b (s.val+1),
   NCV_ZeroStep.byte b (s.val+2), NCV_ZeroStep.byte b (s.val+3)]
 have window : NDB_PrimaryWords.window b s.val 4#usize = a := by
  apply Subtype.ext
  rfl
 refine ⟨core.num.U32.from_le_bytes a, ?_, ?_⟩
 · rw [NDB_PrimaryWords.word32 b s fit, window]
 · exact NMX_R3_Word32.fixed _ _ _ _
#print axioms value
end NMX_R3_WordRead
