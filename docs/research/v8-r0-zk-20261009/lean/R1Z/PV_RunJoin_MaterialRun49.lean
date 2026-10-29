import R1Z.PV_RunJoin_MaterialVec49
import R1Z.PV_RunJoin_WeightResult46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MaterialRun49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_RunJoin_WeightMap46 (mapResult)
open PV_RunJoin_MaterialVec49 (S vec)

def outcome (request : Result PV_B2_F_AllocationTransport.Outcome)
    (r : Result (Array S 1024#usize)) : Result (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact) verifier.Error) := do
  let event ← request
  match event with
  | .denied => ok (.Err .Allocation)
  | .supplied => do let a ← r;ok (.Ok (vec a))

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (w : PV_RunJoin_WeightCarrier46.W) (hs : w.variant=.S2) (x : S) :
    @ExternalFuns.op251 (types base) (selected base heap box ops) w (ProverRwDictionaryTower.fromW x)=
      outcome (heap w (ProverRwDictionaryTower.fromW x))
        (ProverCommitWeightsMaterialBinding53.run (PV_RunJoin_WeightCarrier46.state w) x) := by
  rw [PV_RunJoin_WeightMaterialInstalled47.complete base heap box ops w hs]
  unfold PV_RunJoin_WeightMaterialResult47.run outcome
  rw [PV_RunJoin_MaterialVec49.input,PV_RunJoin_WeightResult46.shared_bind]
  apply congrArg (Aeneas.Std.bind _)
  funext event
  cases event with
  | denied => rfl
  | supplied => exact PV_RunJoin_MaterialVec49.wrap _
#print axioms outcome
#print axioms complete
end R1Z.PV_RunJoin_MaterialRun49
