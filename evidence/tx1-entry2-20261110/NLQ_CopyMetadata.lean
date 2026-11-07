import NLQ_CopyFrame
set_option autoImplicit false
namespace NLQ_CopyMetadata
open NLF_RefCell NLF_SdkModel
/-- Full value post of a completed copy/Drop. -/
def post (s : State) (a : Nat) (src : List UInt8) : State :=
 put s (s.accounts a).data {s.cells (s.accounts a).data with
  payload:={(s.cells (s.accounts a).data).payload with bytes:=src}}
theorem accounts (s : State) (a : Nat) (src : List UInt8) :
 (post s a src).accounts=s.accounts := rfl
/-- All cells' money and borrow ownership survive the returning copy, even
before caller-specific key/cell disjointness is applied to byte payloads. -/
theorem cell (s : State) (a c : Nat) (src : List UInt8) :
 ((post s a src).cells c).payload.money=(s.cells c).payload.money ∧
 ((post s a src).cells c).readers=(s.cells c).readers ∧
 ((post s a src).cells c).writer=(s.cells c).writer := by
 by_cases same : c=(s.accounts a).data <;> simp [post,put,same]
#print axioms accounts
#print axioms cell
end NLQ_CopyMetadata
