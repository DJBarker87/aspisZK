import NMT_345TailTagRead
import NMT_345TailTagExpected
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepTagRead {W : Type} (c : Calls) (s : TagOffset W) :
 tailTagRead c s = (do let tag ← Slice.index_usize s.proofData s.tagOffset; tailTagExpected c ⟨s,tag⟩) := rfl
#print axioms stepTagRead
end NMT_345
