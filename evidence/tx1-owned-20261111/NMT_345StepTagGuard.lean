import NMT_345TailTagReply
import NMT_345TailSemanticRead
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepTagGuard {W : Type} (c : Calls) (s : TagExpected W) :
 tailTagReply c s = if s.tagByte != s.expectedTag then .ok (.Err .InvalidAccountData) else tailSemanticRead c s := rfl
#print axioms stepTagGuard
end NMT_345
