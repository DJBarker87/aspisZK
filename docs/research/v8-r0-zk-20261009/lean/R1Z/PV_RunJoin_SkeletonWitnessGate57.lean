import R1Z.PV_RunJoin_QuerySuccessfulObstruction57
import R1Z.PV_RunJoin_PublishContext57
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SkeletonWitnessGate57
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

/-- The full range-only conjunction, including both publication appends. -/
def RangeLinks {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_Link_R24Sampler ∧
  PV_RunJoin_Link_CommonSample runs ∧ PV_RunJoin_Link_BackendInput runs ∧
  PV_RunJoin_Link_FinishContext runs ∧
  PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryRange runs ∧
  PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryAppend runs ∧
  PV_RunJoin_Link_NodeAppend runs ∧
  PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_PublishOrder runs

/-- The second candidate's complete witness obligation. No witness is claimed. -/
def ContextLinks {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_Link_R24Sampler ∧
  PV_RunJoin_Link_CommonSample runs ∧ PV_RunJoin_Link_BackendInput runs ∧
  PV_RunJoin_Link_FinishContext runs ∧
  PV_RunJoin_PublishContext57.PV_RunJoin_Link_QueryContext runs ∧
  PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryRange runs ∧
  PV_RunJoin_PublishContext57.PV_RunJoin_Link_QueryAppend runs ∧
  PV_RunJoin_Link_NodeAppend runs ∧
  PV_RunJoin_PublishContext57.PV_RunJoin_Link_PublishOrder runs

theorem range_no_successful_witness {I : Type}
    (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (i : I) (proof : alloc.vec.Vec U8)
    (success : @source (types base) (selected base heap box ops) (runs i)=ok (.Ok proof))
    (bound : (@Run.plan (types base) (runs i)).offOpenings≤Usize.max) :
    ¬@RangeLinks (types base) (selected base heap box ops) I runs := by
  rintro ⟨_,common,backend,finish,_,query,_,_⟩
  exact PV_RunJoin_QuerySuccessfulObstruction57.complete base heap box ops runs
    common backend finish query i proof success bound

#print axioms RangeLinks
#print axioms ContextLinks
#print axioms range_no_successful_witness
end R1Z.PV_RunJoin_SkeletonWitnessGate57
