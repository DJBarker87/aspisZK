import NKK_AllocationStage
set_option autoImplicit false
noncomputable section
namespace NKK_AllocationStage
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

/-- The width needed by the entered weights child is derived from this
actual allocation result, not supplied as a root premise. -/
theorem width (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (values : alloc.vec.Vec K)
 (returned : (source reservation d).result=ok (.Ok values)) : values.val.length=64 := by
 cases reservation with
 | Err err => rw [rejected] at returned;cases returned
 | Ok unit =>
  cases unit
  have same:=core.result.Result.Ok.inj (Result.ok.inj returned)
  have size:=congrArg (fun v : alloc.vec.Vec K=>v.val.length) same
  change (List.replicate 64 zero).length=values.val.length at size
  rw [List.length_replicate] at size
  exact size.symm

#print axioms width
end NKK_AllocationStage
