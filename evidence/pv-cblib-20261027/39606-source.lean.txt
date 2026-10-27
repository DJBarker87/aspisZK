import R1Z.PV_CBL_Op34Reference
import R1Z.PV_CBL_VectorShape
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op34Transport
set_option autoImplicit false

theorem reference_eq {T : Type} (v : alloc.vec.Vec T) :
    PV_CBL_Op34Reference.empty_reference v =
      PV_CBL_VectorShape.emptyReference v := by
  unfold PV_CBL_Op34Reference.empty_reference PV_CBL_VectorShape.emptyReference
  apply congrArg Result.ok
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq]
#print axioms reference_eq
end R1Z.PV_CBL_Op34Transport
