import NKO_C06Result
set_option autoImplicit false
noncomputable section
namespace NKO_StageG
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)
/-- C05 pending-boundary G. Success retains the SAME owned geometry;
error has no returned geometry carrier. Native descriptors/drop stay in K026. -/
def geometry (before : verifier.QueryGeometry) (reply : R verifier.BatchedWeights) :
 R (verifier.QueryGeometry × verifier.BatchedWeights) := do
 let r ← reply
 match r with | .Err e => ok (.Err e) | .Ok b => ok (.Ok (before,b))

def geometrySource (before : verifier.QueryGeometry) (reply : R verifier.BatchedWeights) :
 R (verifier.QueryGeometry × verifier.BatchedWeights) := do
 let r ← reply
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue b => ok (.Ok (before,b))
 | .Break residual =>
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   _ (core.convert.FromSame verifier.Error) residual

theorem geometry_source (before : verifier.QueryGeometry) (reply : R verifier.BatchedWeights) :
 geometrySource before reply=geometry before reply := by
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

def pendingSource (reply : R verifier.BatchedWeights) : R verifier.BatchedWeights := do
 let r ← reply
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue b => ok (.Ok b)
 | .Break residual =>
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   _ (core.convert.FromSame verifier.Error) residual

theorem pending_source (reply : R verifier.BatchedWeights) : pendingSource reply=reply := by
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok r => cases r <;> rfl

/-- Actual full caller-boundary stages have no success-only projection. -/
theorem geometry_error (before : verifier.QueryGeometry) (e : verifier.Error) :
 geometry before (ok (.Err e))=ok (.Err e) := rfl

theorem geometry_success (before : verifier.QueryGeometry) (b : verifier.BatchedWeights) :
 geometry before (ok (.Ok b))=ok (.Ok (before,b)) := rfl
#print axioms geometry_source
#print axioms pending_source
#print axioms geometry_error
#print axioms geometry_success
end NKO_StageG
