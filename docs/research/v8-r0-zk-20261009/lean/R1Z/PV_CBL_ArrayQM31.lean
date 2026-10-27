import R1Z.PV_CBL_ArrayDeterminism
import R1Z.ProverRwFullTypes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayQM31
set_option autoImplicit false
abbrev Q := ProverRwFull.aspis_core.field.QM31

def zero : Q := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

/-- Copy is an unused marker argument in this extracted kernel. This local
value gives a closed presentation; marker_irrelevant proves independence
from its clone field, including the actual generated Copy instance. -/
def marker : core.marker.Copy Q := {cloneInst := {clone := fun x => ok x}}

def reference (v : Slice Q) : Result (Option (Array Q 1024#usize)) :=
  PV_CBL_ArrayKernel.array_reference 1024#usize marker v zero

theorem marker_irrelevant (actual : core.marker.Copy Q) (v : Slice Q) :
    PV_CBL_ArrayKernel.array_reference 1024#usize actual v zero = reference v := rfl

theorem success (v : Slice Q) (h : Slice.len v=1024#usize) :
    ∃ a, reference v=ok (some a) ∧ a.val=v.val :=
  PV_CBL_ArraySuccess.success 1024#usize marker v zero h

theorem reject (v : Slice Q) (h : Slice.len v≠1024#usize) : reference v=ok none :=
  PV_CBL_ArrayGuard.wrong_length 1024#usize marker v zero h
#print axioms zero
#print axioms marker
#print axioms reference
#print axioms marker_irrelevant
#print axioms success
#print axioms reject
end R1Z.PV_CBL_ArrayQM31
