import R1Z.PV_RunJoin_PublishSkeleton54
import R1Z.PV_RunJoin_R24Complete54
import R1Z.PV_RunJoin_SamplerCanonical54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LinkR24Discharged54
open ProverRwFull PV_RunJoin_WeightInstalled46 PV_RunJoin_PublishSkeleton54

theorem complete : PV_RunJoin_Link_R24Sampler :=
  ⟨PV_RunJoin_R24Complete54.complete,PV_RunJoin_SamplerCanonical54.complete⟩

theorem publication {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) I runs)
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) I runs)
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) I runs)
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) I runs)
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) I runs)
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) I runs) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops) I runs)
      (@published (types base) (selected base heap box ops) I runs) :=
  PV_RunJoin_PublishSkeleton54.complete base heap box ops runs complete common backend finish query node ordering
#print axioms complete
#print axioms publication
end R1Z.PV_RunJoin_LinkR24Discharged54
