import NMT_345Route10
import NMT_345RawSelected
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- One guard and the actual three reads; the child-bearing remainder stays
opaque. This is exact source factoring, with no call-tree erasure. -/
theorem admitted_select {W : Type} (c : Calls) (s : Parent W) :
 admitted c s =
 if Slice.len s.accounts != 3#usize then .ok (.Err .InvalidInstructionData)
 else select s (rawSelected c) := rfl
#print axioms admitted_select
end NMT_345
