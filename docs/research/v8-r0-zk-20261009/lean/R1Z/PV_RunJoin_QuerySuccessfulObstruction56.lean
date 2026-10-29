import R1Z.PV_RunJoin_QueryNativeObstruction56
import R1Z.PV_RunJoin_LinkR24Discharged54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QuerySuccessfulObstruction56
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54

theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) I runs)
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) I runs)
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) I runs)
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) I runs)
    (i : I) (proof : alloc.vec.Vec U8)
    (success : @source (types base) (selected base heap box ops) (runs i)=ok (.Ok proof))
    (bound : (@Run.plan (types base) (runs i)).offOpenings≤Usize.max) : False := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  obtain ⟨prepared,salts,p,hp,hsalts,hf,hpub⟩ := PV_RunJoin_PublishReach54.complete
    (runs i).public1 .S2 (runs i).hash (runs i).backend (runs i).sem (runs i).salts proof success
  obtain ⟨hc,hinput,hlen⟩ := backend i prepared hp
  have sample := (common PV_RunJoin_LinkR24Discharged54.complete i prepared hp).1
  have images := PV_RunJoin_OpeningImages54.complete (runs i).data hc sample
  have small : (alloc.vec.Vec.deref (runs i).backend.messages).length≤14336 := by
    change (runs i).backend.messages.length≤14336
    rw [hlen]; omega
  have coeff : CoefficientCaller (runs i) :=
    PV_RunJoin_CoefficientsActual50.complete base heap box ops
      (alloc.vec.Vec.deref (runs i).backend.messages) small
  have fields := finish i prepared salts p hc hp hsalts hf coeff images
  exact PV_RunJoin_QueryNativeObstruction56.complete base heap box ops runs i p fields bound query

#print axioms complete
end R1Z.PV_RunJoin_QuerySuccessfulObstruction56
