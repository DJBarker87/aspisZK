import NMT_345TailPrefixReply
import NMT_345TailTagOffset
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepPrefixGuard {W : Type} (c : Calls) (s : PrefixReply W) :
 tailPrefixReply c s = if s.prefixMismatch then .ok (.Err .InvalidAccountData) else tailTagOffset c s := rfl
#print axioms stepPrefixGuard
end NMT_345
