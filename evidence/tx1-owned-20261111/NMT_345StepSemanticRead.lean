import NMT_345TailSemanticRead
import NMT_345TailProofRange
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem stepSemanticRead {W : Type} (c : Calls) (s : TagExpected W) :
 tailSemanticRead c s = (do let pub ← c.c5 s.statement; tailProofRange c ⟨s,pub⟩) := rfl
#print axioms stepSemanticRead
end NMT_345
