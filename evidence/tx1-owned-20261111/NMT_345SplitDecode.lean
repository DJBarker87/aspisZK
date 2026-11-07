import NMT_345StepBase
import NMT_345Distinct
import NMT_345Raw_06
import NMT_345Raw_07
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitDecode {W : Type} (c : Calls) (s : PublicData W) :
 raw06 c s = tryStep (c.c12 s.publicData) (fun statement => raw07 c ⟨s,statement⟩) :=
 emitted_try _ _
#print axioms splitDecode
end NMT_345
