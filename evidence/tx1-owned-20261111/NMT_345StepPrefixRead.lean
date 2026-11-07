import NMT_345TailPrefixRead
import NMT_345TailPrefixCompare
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepPrefixRead {W : Type} (c : Calls) (s : Bounds W) :
 tailPrefixRead c s = (do let proofPrefix ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) s.proofData { «end» := s.proofStart }; tailPrefixCompare c ⟨s,proofPrefix⟩) := rfl
#print axioms stepPrefixRead
end NMT_345
