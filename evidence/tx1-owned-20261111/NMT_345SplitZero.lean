import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_04
import NMT_345Raw_05
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitZero {W : Type} (c : Calls) (s : CheckpointData W) :
 raw04 c s = tryStep (c.c16 s.checkpointData) (fun _ => raw05 c s) :=
 emitted_try _ _
#print axioms splitZero
end NMT_345
