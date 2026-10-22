import AspisR1S9CandidateHelperV1.Funs
import AspisR1S9HelperP6.Funs

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidatePerm3BridgeV1

/-- The pinned candidate and P6 helper tables contain the same PERM[3]
entry. This transports the already-bound candidate witness without choosing
or normalizing a new query index. -/
theorem candidate_perm3_read_transports (x : Std.Usize)
    (h : Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM
      3#usize = .ok x) :
    Array.index_usize _root_.AspisR1S9HelperP6.weights.PERM 3#usize = .ok x := by
  simpa [_root_.AspisR1S9CandidateHelperV1.weights.PERM,
    _root_.AspisR1S9HelperP6.weights.PERM] using h

#print axioms candidate_perm3_read_transports

end AspisR1S9CandidatePerm3BridgeV1
