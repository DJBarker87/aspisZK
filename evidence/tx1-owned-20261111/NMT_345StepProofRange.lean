import NMT_345TailProofRange
import NMT_345TailSplitByte
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepProofRange {W : Type} (c : Calls) (s : HasPublic W) :
 tailProofRange c s = (do let proof ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s.proofData {start := s.proofStart, «end» := s.proofEnd}; tailSplitByte c ⟨s,proof⟩) := rfl
#print axioms stepProofRange
end NMT_345
