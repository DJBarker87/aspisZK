import NMT_345Raw_11
import NMT_345TailPrefixRead
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepLengthGuard {W : Type} (c : Calls) (s : Bounds W) :
 raw11 c s = if Slice.len s.proofData != s.proofEnd then .ok (.Err .InvalidAccountData) else tailPrefixRead c s := rfl
#print axioms stepLengthGuard
end NMT_345
