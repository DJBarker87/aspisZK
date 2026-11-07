import NMT_345TailTagOffset
import NMT_345TailTagRead
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepTagOffset {W : Type} (c : Calls) (s : PrefixReply W) :
 tailTagOffset c s = (do let offset ← lift (Usize.wrapping_add s.proofStart 8#usize); tailTagRead c ⟨s,offset⟩) := rfl
#print axioms stepTagOffset
end NMT_345
