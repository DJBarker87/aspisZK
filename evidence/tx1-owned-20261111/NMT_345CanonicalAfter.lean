import NMT_345CanonicalContainers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Existing CLOSED afterstate validator's own returning-arm invariant. -/
theorem after_canonical (a : NFY_NBH_Validators.Afterstate)
 (h : NFY_NBH_Validators.afterResult a = .Ok ()) :
 NBD_DigestInduction.Canonical a.next_root ∧ NBH_Frontier.CanonicalFrom a.next_frontier 0 := by
 unfold NFY_NBH_Validators.afterResult at h
 split at h
 · cases h
 · split at h
   · assumption
   · cases h
#print axioms after_canonical
end NMT_345
