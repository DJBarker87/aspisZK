import NMT_345StepBase
import NMT_345Distinct
import NMT_345RawSelected
import NMT_345Raw_00
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One actual emitted call occurrence. The suffix stays a named opaque
continuation over the same full parent state; every Result arm is exact. -/
theorem splitSelected {W : Type} (c : Calls) (s : Selected W) :
 rawSelected c s = tryStep (c.c15 (selectedArray s)) (fun _ => raw00 c s) :=
 emitted_try (c.c15 (selectedArray s)) (fun _ => raw00 c s)
#print axioms splitSelected
end NMT_345
