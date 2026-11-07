import NMT_345BoundaryCheckpoint
import NMT_R2_EmittedCheckpoint
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtCheckpoint
open Aeneas Aeneas.Std NMT_345 RSL

def install (keep : Bool) (c : Calls) : Calls :=
 {c with c14 := fun a program writable =>
  mapOuter (mapCore id fromPE) (NMT_R2_CheckpointEquation.native keep a program writable)}

/-- Actual E003 occurrence c14, SAME complete selected parent. -/
theorem boundary {W : Type} (keep : Bool) (c : Calls) (s : Selected W) :
 raw02 (install keep c) s =
 tryStep (mapOuter (mapCore id fromPE)
  (NMT_R2_CheckpointEquation.native keep s.checkpointAccount s.program true))
  (fun _ => raw03 (install keep c) s) := boundaryCheckpoint _ s

theorem observation {W : Type} (keep : Bool) (s : Selected W) (env : Env) :
 NMT_R2.verifierCheckpoint (account s.checkpointAccount) (key s.program) true env
  (NMT_R2_EmittedCheckpoint.run keep s.checkpointAccount s.program true) :=
 NMT_R2_EmittedCheckpoint.emitted_checkpoint keep s.checkpointAccount s.program true env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtCheckpoint
end
