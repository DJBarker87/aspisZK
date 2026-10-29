import R1Z.PV_RunJoin_PublishSkeleton54
/-! D485 repair: the query bound is strict, from r0::FIBRE_COUNT=1<<18.
This is a candidate conditional interface; no decomposition credit without
an explicit simultaneous-link witness. The historical skeleton is retained. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublishSkeleton57
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
variable [ExternalTypes] [ExternalFuns]

def QueryRange (queries : Array U32 22#usize) : Prop :=
  ∀ q ∈ queries.val, q.val < 262144

def PV_RunJoin_Link_QueryRange {I : Type} (runs : I → Run) : Prop :=
  ∀ i (prepared : prover.PreparedOpening) (salts : host_commitment.PrivateSalts)
    (p : prover.Publication),
    prover.prepare_opening .S2 (runs i).hash (runs i).backend (runs i).sem=ok (.Ok prepared) →
    prover.derive_private_salts (runs i).salts.1 (runs i).salts.2 (runs i).hash 114#u8=ok (.Ok salts) →
    prover.finish_opening .S2 (runs i).hash prepared salts=ok (.Ok p) → QueryRange p.queries

def PV_RunJoin_Link_QueryAppend {I : Type} (runs : I → Run) : Prop :=
  ∀ i (p : prover.Publication), Fields (runs i) p → QueryRange p.queries →
  (runs i).plan.queries.length=22 ∧ ∀ out cc1 cc2,
    p.backend.c1=some cc1 → p.backend.c2=some cc2 → out.length=(runs i).plan.offOpenings →
    ∃ next, prover.append_query_openings out cc1 cc2 p.queries
      (alloc.vec.Vec.deref p.folded_word) p.folded_salts=ok next ∧
      bytes next.val=ProverCommitPublish43.queries (runs i).plan.queries (bytes out.val)

/-- Local serializer ordering, not the complete actual-run conclusion. -/
def PV_RunJoin_Link_PublishOrder {I : Type} (runs : I → Run) : Prop :=
  PV_RunJoin_Link_QueryAppend runs → PV_RunJoin_Link_NodeAppend runs →
  ∀ i (p : prover.Publication) (proof : alloc.vec.Vec U8), Fields (runs i) p → QueryRange p.queries →
    prover.publish_compact .S2 p=ok (.Ok proof) →
    ProverCommitPublish43.assembleLoop (.ok (front (runs i))) (runs i).plan.queries (runs i).plan.slots
      (runs i).plan.offNodes (runs i).plan.proofBytes=.ok (bytes proof.val)

theorem complete {I : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (runs : I → @Run (types base))
    (r24 : PV_RunJoin_Link_R24Sampler)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) I runs)
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) I runs)
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) I runs)
    (range : @PV_RunJoin_Link_QueryRange (types base) (selected base heap box ops) I runs)
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) I runs)
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) I runs)
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) I runs) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops) I runs)
      (@published (types base) (selected base heap box ops) I runs) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
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
      have assembled := ordering query node i p proof fields qr hpub
      rw [ProverCommitPublish43.assemble_loop] at assembled
      have ha : assembly (runs i)=.ok (bytes proof.val) := assembled
      simp only [actual,published,hs,resultBytes,ha,exceptBytes,Option.map_some,publication,PV_RJ4IDB.PublicationInput.publish_compact]

#print axioms QueryRange
#print axioms PV_RunJoin_Link_QueryRange
#print axioms PV_RunJoin_Link_QueryAppend
#print axioms PV_RunJoin_Link_PublishOrder
#print axioms complete
end R1Z.PV_RunJoin_PublishSkeleton57
