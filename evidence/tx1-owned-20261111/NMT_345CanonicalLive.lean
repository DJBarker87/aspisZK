import NMT_345CanonicalContainers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Existing CLOSED live validator's own returning-arm invariant. -/
theorem live_canonical (s : NFY_NBH_LiveValidator.Snapshot)
 (h : NFY_NBH_LiveValidator.result s = .Ok ()) :
 NBD_DigestInduction.Canonical s.current_root ∧ NBH_Frontier.CanonicalFrom s.frontier 0 := by
 unfold NFY_NBH_LiveValidator.result at h
 split at h
 · cases h
 · split at h
   · cases h
   · split at h
     · cases h
     · split at h
       · assumption
       · cases h
#print axioms live_canonical
end NMT_345
