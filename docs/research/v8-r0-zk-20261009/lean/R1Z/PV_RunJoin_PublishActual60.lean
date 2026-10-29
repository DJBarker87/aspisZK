import R1Z.PV_RunJoin_ActualRun
import R1Z.PV_RJN_NodeContext
/-! ActualRun publication interface. Historical interfaces stay available for
counterexample auditing. No simultaneous-link witness is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublishActual60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

abbrev runs := PV_RunJoin_ActualRun.runs
abbrev PV_RunJoin_Link_R24Sampler := PV_RunJoin_PublishSkeleton54.PV_RunJoin_Link_R24Sampler
abbrev PV_RunJoin_Link_CommonSample := PV_RunJoin_PublishSkeleton54.PV_RunJoin_Link_CommonSample runs
abbrev PV_RunJoin_Link_BackendInput := PV_RunJoin_PublishSkeleton54.PV_RunJoin_Link_BackendInput runs
abbrev PV_RunJoin_Link_FinishContext := PV_RunJoin_PublishSkeleton54.PV_RunJoin_Link_FinishContext runs
abbrev PV_RunJoin_Link_QueryContext := PV_RunJoin_PublishContext57.PV_RunJoin_Link_QueryContext runs
abbrev PV_RunJoin_Link_QueryRange := PV_RunJoin_PublishSkeleton57.PV_RunJoin_Link_QueryRange runs
abbrev PV_RunJoin_Link_QueryAppend := PV_RunJoin_PublishContext57.PV_RunJoin_Link_QueryAppend runs
abbrev PV_RunJoin_Link_NodeAppend := PV_RJN_NodeContext.PV_RJN_Link_NodeAppend runs
abbrev PV_RunJoin_Link_PublishOrder := PV_RJN_NodeContext.PV_RJN_Link_PublishOrder runs

def Links : Prop :=
  PV_RunJoin_Link_R24Sampler ∧ PV_RunJoin_Link_CommonSample ∧
  PV_RunJoin_Link_BackendInput ∧ PV_RunJoin_Link_FinishContext ∧
  PV_RunJoin_Link_QueryContext ∧ PV_RunJoin_Link_QueryRange ∧
  PV_RunJoin_Link_QueryAppend ∧ PV_RunJoin_Link_NodeAppend ∧ PV_RunJoin_Link_PublishOrder

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (r24 : PV_RunJoin_Link_R24Sampler)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops))
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops))
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops))
    (context : @PV_RunJoin_Link_QueryContext (types base) (selected base heap box ops))
    (range : @PV_RunJoin_Link_QueryRange (types base) (selected base heap box ops))
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops))
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops))
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops))
    : PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops) _ (@runs (types base) (selected base heap box ops)))
      (@published (types base) (selected base heap box ops) _ (@runs (types base) (selected base heap box ops))) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  let runs := PV_RunJoin_ActualRun.runs
  intro i
  cases hs : source (runs i) with
  | fail e => simp only [actual,published,hs,resultBytes,Option.map_none]
  | div => simp only [actual,published,hs,resultBytes,Option.map_none]
  | ok result =>
    cases result with
    | Err e => simp only [actual,published,hs,resultBytes,Option.map_none]
    | Ok proof =>
      obtain ⟨prepared,salts,p,hp,hsalts,hf,hpub⟩ := PV_RunJoin_PublishReach54.complete
        (runs i).public1 .S2 (runs i).hash (runs i).backend (runs i).sem (runs i).salts proof hs
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
      have qr := range i prepared salts p hp hsalts hf
      have qc := context i prepared salts p hp hsalts hf
      have assembled := ordering query node i p proof fields qr qc hpub
      rw [ProverCommitPublish43.assemble_loop] at assembled
      have ha : assembly (runs i)=.ok (bytes proof.val) := assembled
      simp only [actual,published,hs,resultBytes,ha,exceptBytes,Option.map_some,publication,PV_RJ4IDB.PublicationInput.publish_compact]


#print axioms complete
#print axioms Links
end R1Z.PV_RunJoin_PublishActual60
