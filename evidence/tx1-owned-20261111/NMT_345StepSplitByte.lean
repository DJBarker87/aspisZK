import NMT_345TailSplitByte
import NMT_345TailSplitCast
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepSplitByte {W : Type} (c : Calls) (s : HasProofSlice W) :
 tailSplitByte c s = (do let kbyte ← Slice.index_usize s.data 1#usize; tailSplitCast c ⟨s,kbyte⟩) := rfl
#print axioms stepSplitByte
end NMT_345
