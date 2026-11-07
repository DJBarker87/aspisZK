import NMT_345BoundaryZero
import NMT_345ZeroSource
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result

def installZero (c : Calls) : Calls := {c with c16 := zeroCall}
theorem install_zero {W : Type} (c : Calls) (s : CheckpointData W) :
 raw04 (installZero c) s =
 if s.checkpointData.val.all (· == 0#u8)
 then raw05 (installZero c) s else .ok (.Err .AccountAlreadyInitialized) := by
 rw [boundaryZero]
 change zeroStep s (raw05 (installZero c)) = _
 exact zeroStep_value _ _
#print axioms install_zero
end NMT_345
