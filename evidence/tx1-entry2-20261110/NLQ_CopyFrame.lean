import NLQ_CopyTrace
set_option autoImplicit false
namespace NLQ_CopyFrame
open NLF_RefCell NLF_SdkModel
/-- A returned copy changes only the selected cell payload. All accounts,
lamports, metadata and nonselected cell contents remain exact. -/
theorem copied_cell (s : State) (a t : Nat) (src : List UInt8)
 (free : (s.cells (s.accounts a).data).writer=none)
 (empty : (s.cells (s.accounts a).data).readers=[])
 (same : src.length=(s.cells (s.accounts a).data).payload.bytes.length) :
 (NLQ_CopyTrace.G s a t src).outcome =
 .returned (put s (s.accounts a).data {s.cells (s.accounts a).data with
   payload:={(s.cells (s.accounts a).data).payload with bytes:=src}}) (.ok ()) := by
 rw [NLQ_CopyTrace.erasure]
 exact NLF_CopyStep.success s a t src free empty same
/-- Full-cell rather than address frame. This is a value law; native byte
windows and the caller's guard/alias domain are separately required. -/
theorem outside (s : State) (a c : Nat) (src : List UInt8)
 (different : c≠(s.accounts a).data) :
 (put s (s.accounts a).data {s.cells (s.accounts a).data with
   payload:={(s.cells (s.accounts a).data).payload with bytes:=src}}).cells c = s.cells c := by
 simp [put,different]
#print axioms copied_cell
#print axioms outside
end NLQ_CopyFrame
