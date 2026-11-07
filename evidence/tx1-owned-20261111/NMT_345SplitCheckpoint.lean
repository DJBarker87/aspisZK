import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_02
import NMT_345Raw_03
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitCheckpoint {W : Type} (c : Calls) (s : Selected W) :
 raw02 c s = tryStep (c.c14 s.checkpointAccount s.program true) (fun _ => raw03 c s) :=
 emitted_try _ _
#print axioms splitCheckpoint
end NMT_345
