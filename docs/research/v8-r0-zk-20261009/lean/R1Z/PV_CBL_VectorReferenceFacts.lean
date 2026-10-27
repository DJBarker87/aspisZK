import R1Z.PV_CBL_Op34Transport
import R1Z.PV_CBL_Op35Reference
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_VectorReferenceFacts
set_option autoImplicit false

/-- Neither native reference inspects the element payload. -/
theorem empty_new (T : Type) :
    PV_CBL_Op34Reference.empty_reference (alloc.vec.Vec.new T) = ok true := by
  have hz : alloc.vec.Vec.len (alloc.vec.Vec.new T) = 0#usize := by scalar_tac
  simp only [PV_CBL_Op34Reference.empty_reference, hz, decide_true]

theorem default_len_zero (T : Type) :
    (do let v ← PV_CBL_Op35Reference.default_reference T
        ok (alloc.vec.Vec.len v)) = ok 0#usize := by
  change ok (alloc.vec.Vec.len (alloc.vec.Vec.new T)) = ok 0#usize
  congr 1

theorem empty_failure_impossible {T : Type} (v : alloc.vec.Vec T) (e : Error) :
    PV_CBL_Op34Reference.empty_reference v ≠ fail e := by
  simp [PV_CBL_Op34Reference.empty_reference]

theorem empty_divergence_impossible {T : Type} (v : alloc.vec.Vec T) :
    PV_CBL_Op34Reference.empty_reference v ≠ div := by
  simp [PV_CBL_Op34Reference.empty_reference]

#print axioms empty_new
#print axioms default_len_zero
#print axioms empty_failure_impossible
#print axioms empty_divergence_impossible
end R1Z.PV_CBL_VectorReferenceFacts
