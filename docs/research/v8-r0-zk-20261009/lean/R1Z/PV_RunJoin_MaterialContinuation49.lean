import R1Z.PV_RunJoin_MaterialRun49
import R1Z.PV_RunJoin_PrepareMaterialContext49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialContinuation49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_MaterialVec49 (S W vec)
variable [ExternalTypes] [ExternalFuns]
def run (material : Result (core.result.Result (alloc.vec.Vec W) verifier.Error))
    (tail : Slice W → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    Result (core.result.Result prover.PreparedOpening verifier.Error) := do
  let r ← material
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue v => tail (alloc.vec.Vec.deref v)
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      prover.PreparedOpening (core.convert.FromSame verifier.Error) residual

theorem supplied (a : Array S 1024#usize)
    (tail : Slice W → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    run (ok (.Ok (vec a))) tail=tail (alloc.vec.Vec.deref (vec a)) := rfl

theorem denied (tail : Slice W → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    run (ok (.Err .Allocation)) tail=ok (.Err .Allocation) := rfl

theorem complete (request : Result PV_B2_F_AllocationTransport.Outcome) (r : Result (Array S 1024#usize))
    (tail : Slice W → Result (core.result.Result prover.PreparedOpening verifier.Error)) :
    run (PV_RunJoin_MaterialRun49.outcome request r) tail=
      (do let event ← request
          match event with
          | .denied => ok (.Err .Allocation)
          | .supplied => do let a ← r;tail (alloc.vec.Vec.deref (vec a))) := by
  cases request with
  | fail e => rfl
  | div => rfl
  | ok event =>
    cases event with
    | denied => exact denied tail
    | supplied =>
      cases r with
      | fail e => rfl
      | div => rfl
      | ok a => exact supplied a tail
#print axioms run
#print axioms supplied
#print axioms denied
#print axioms complete
end R1Z.PV_RunJoin_MaterialContinuation49
