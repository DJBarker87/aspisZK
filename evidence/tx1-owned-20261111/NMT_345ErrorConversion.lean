import NMT_345StepBase
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
set_option pp.fullNames true in
#print Aeneas.Std.core.convert.FromSame
set_option pp.fullNames true in
#check (Aeneas.Std.core.convert.FromSame PE).from
/-- The exact std owner used by the fresh emission. -/
theorem from_same_exact (e : PE) :
 (Aeneas.Std.core.convert.FromSame PE).from e = .ok e := by
 rfl
#print axioms from_same_exact
end NMT_345
