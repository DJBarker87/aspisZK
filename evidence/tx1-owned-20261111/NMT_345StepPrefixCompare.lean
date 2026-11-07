import NMT_345TailPrefixCompare
import NMT_345TailPrefixReply
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepPrefixCompare {W : Type} (c : Calls) (s : HasPrefix W) :
 tailPrefixCompare c s = (do let mismatch ← c.c0 core.cmp.PartialEqU8 s.proofPrefix s.candidate; tailPrefixReply c ⟨s,mismatch⟩) := rfl
#print axioms stepPrefixCompare
end NMT_345
