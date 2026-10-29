import R1Z.PV_RunJoin_NativeAttemptLaws55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeAttemptPublication55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_NativeAttemptControl55 (Store storeInst)

structure Input [ExternalTypes] where
  public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  hash : aspis_core.digest.LegacyHashFn
  attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
  store : Store

def execute [ExternalTypes] [ExternalFuns] (i : Input) :=
  prover.prove_masked_attempt i.public1 i.compiled .S2 i.hash i.attempt i.store

def modelExecute [ExternalTypes] [ExternalFuns]
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan) (i : Input) :=
  PV_RunJoin_NativeAttemptControl55.run (PV_RunJoin_NativePublication55.modelExecute data plans storeInst)
    i.public1 i.compiled i.hash i.attempt i.store

def actual [ExternalTypes] [ExternalFuns] (i : Input) :=
  PV_RunJoin_NativeProjection55.observe PV_RunJoin_NativeCallback55.decode (execute i)

def published [ExternalTypes] [ExternalFuns]
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan) (i : Input) :=
  PV_RunJoin_NativeProjection55.observe id (modelExecute data plans i)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (data : @Phase (types base) → PV_RunJoin_OpeningImages54.Data)
    (plans : @Phase (types base) → Plan)
    (common : @PV_RunJoin_Link_CommonSample (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (backend : @PV_RunJoin_Link_BackendInput (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (finish : @PV_RunJoin_Link_FinishContext (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (query : @PV_RunJoin_Link_QueryAppend (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (node : @PV_RunJoin_Link_NodeAppend (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
    (ordering : @PV_RunJoin_Link_PublishOrder (types base) (selected base heap box ops) (@Phase (types base)) (@PV_RunJoin_NativeCallback55.runOf (types base) data plans))
 :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops))
      (@published (types base) (selected base heap box ops) data plans) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro i
  let R := fun proof pub => PV_RunJoin_NativeCallback55.decode proof=PV_RJ4IDB.PublicationInput.publish_compact pub
  have callback := PV_RunJoin_NativeCallback55.complete base heap box ops data plans common backend finish query node ordering
  have inner : ∀ j : PV_RunJoin_NativePublication55.Input Store,
      PV_RunJoin_ResultRelation55.Rel (PV_RunJoin_NativeResult55.Output R)
        (PV_RunJoin_NativePublication55.execute storeInst j)
        (PV_RunJoin_NativePublication55.modelExecute data plans storeInst j) := by
    intro j
    have transport := PV_RunJoin_NativeVariantTransport55.complete R
      PV_RunJoin_NativeControl55.source (PV_RunJoin_NativeCallback55.model data plans)
      storeInst j.public1 j.compiled .S2 callback j.hash j.context j.binding j.attempt j.store
    rw [← PV_RunJoin_NativeControlSource55.complete] at transport
    exact transport
  have outer := PV_RunJoin_NativeAttemptLaws55.relation R
    (PV_RunJoin_NativePublication55.execute storeInst)
    (PV_RunJoin_NativePublication55.modelExecute data plans storeInst)
    inner i.public1 i.compiled i.hash i.attempt i.store
  rw [← PV_RunJoin_NativeAttemptLaws55.source] at outer
  exact PV_RunJoin_NativeProjection55.complete PV_RunJoin_NativeCallback55.decode
    PV_RJ4IDB.PublicationInput.publish_compact _ _ outer
#print axioms Input
#print axioms execute
#print axioms modelExecute
#print axioms actual
#print axioms published
#print axioms complete
end R1Z.PV_RunJoin_NativeAttemptPublication55
