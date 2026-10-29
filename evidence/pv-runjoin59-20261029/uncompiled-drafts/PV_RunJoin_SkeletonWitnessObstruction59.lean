import R1Z.PV_RunJoin_NodeLinkObstruction59
import R1Z.PV_RunJoin_PublishNodesReach59
import R1Z.PV_RunJoin_SkeletonWitnessGate57
import R1Z.PV_RunJoin_LinkR24Discharged54
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SkeletonWitnessObstruction59
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54

/-- Every successful published run at the actual depth and node offset
refutes the current complete conjunction. This is a link-interface
obstruction, not a privacy counterexample or a claim that an honest run
produces the malformed tree used inside its universal quantifier. -/
theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (i : I) (proof : alloc.vec.Vec U8) (offset : Usize)
    (depth : @multiproof.LEAF_BITS (types base) (selected base heap box ops)=ok 18#u32)
    (hoffset : @compact.OFF_NODES (types base) (selected base heap box ops)=ok offset)
    (layout : (runs i).plan.offNodes=offset.val)
    (success : @source (types base) (selected base heap box ops) (runs i)=ok (.Ok proof)) :
    ¬@PV_RunJoin_SkeletonWitnessGate57.ContextLinks
      (types base) (selected base heap box ops) I runs := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rintro ⟨r24,common,backend,finish,context,range,query,node,ordering⟩
  obtain ⟨prepared,salts,p,hp,hsalts,hf,hpub⟩ := PV_RunJoin_PublishReach54.complete
    (runs i).public1 .S2 (runs i).hash (runs i).backend (runs i).sem (runs i).salts proof success
  obtain ⟨hc,hinput,hlen⟩ := backend i prepared hp
  have sample := (common r24 i prepared hp).1
  have images := PV_RunJoin_OpeningImages54.complete (runs i).data hc sample
  have small : (alloc.vec.Vec.deref (runs i).backend.messages).length≤14336 := by
    change (runs i).backend.messages.length≤14336
    rw [hlen]; omega
  have coeff : CoefficientCaller (runs i) :=
    PV_RunJoin_CoefficientsActual50.complete base heap box ops
      (alloc.vec.Vec.deref (runs i).backend.messages) small
  have fields := finish i prepared salts p hc hp hsalts hf coeff images
  obtain ⟨out,cc1,cc2,hlen,hnodes⟩ := PV_RunJoin_PublishNodesReach59.complete .S2 p proof offset hoffset hpub
  exact PV_RunJoin_NodeLinkObstruction59.complete runs i p fields out proof cc1 cc2
    (hlen.trans layout.symm) depth hnodes node

#print axioms complete
end R1Z.PV_RunJoin_SkeletonWitnessObstruction59
