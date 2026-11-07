import NLW_Full064Fold
set_option autoImplicit false
noncomputable section
namespace NLW_064CandidateFold
open Aeneas Aeneas.Std AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The immutable merged corrected child supplies its stated interface.
This reuse does not confer ledger credit or install the physical parent Frame. -/
theorem child (H : Bytes → State) : ChildBridge H := by
 intro X d pub proof ck hash length bound roots
 exact NLT_CompleteRoot.root H d pub proof ck hash length bound roots
/-- Removes the OPEN-child parameter using the merged gated candidate.
The remaining Invocation premise is still the proposed cut interpretation,
not a proved actual-parent producer; this theorem is NOT a row root. -/
theorem fold {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (publicBound : s.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.args.checkpoint s.args.proof)
 (outcome : End H s.args) (events : List (Event Ambient X))
 (native : Invocation H s outcome events) :
 Law H s.args outcome ∧ events=chronology H s outcome :=
 NLW_Full064.fold H (child H) s publicBound root0 outcome events native
#print child
#print fold
#print axioms child
#print axioms fold
end NLW_064CandidateFold
