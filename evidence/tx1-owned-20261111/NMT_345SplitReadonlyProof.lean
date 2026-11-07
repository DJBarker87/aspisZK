import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_00
import NMT_345Raw_01
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitReadonlyProof {W : Type} (c : Calls) (s : Selected W) :
 raw00 c s = tryStep (c.c13 s.proofAccount) (fun _ => raw01 c s) :=
 emitted_try _ _
#print axioms splitReadonlyProof
end NMT_345
