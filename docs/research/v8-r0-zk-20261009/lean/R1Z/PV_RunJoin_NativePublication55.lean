import R1Z.PV_RunJoin_NativeCallback55
import R1Z.PV_RunJoin_NativeVariantTransport55
import R1Z.PV_RunJoin_NativeControlSource55
import R1Z.PV_RunJoin_NativeProjection55
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativePublication55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_PublishSkeleton54
open PV_RunJoin_NativeControl55 (Phase)

structure Input [ExternalTypes] (T : Type) where
  public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
  compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
  hash : aspis_core.digest.LegacyHashFn
  context : aspis_core.state_only_hiding.StateOnlyHidingContext
  binding : Array U8 32#usize
  attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
  store : T

def execute [ExternalTypes] [ExternalFuns] {T : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) (i : Input T) :=
  prover.prove_masked_with_attempt store i.public1 i.compiled .S2 i.hash i.context i.binding i.attempt i.store

def modelExecute [ExternalTypes] [ExternalFuns] {T : Type}
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) (i : Input T) :=
  PV_RunJoin_NativeControl55.run (PV_RunJoin_NativeCallback55.model data plans)
    store i.public1 i.compiled .S2 i.hash i.context i.binding i.attempt i.store

def actual [ExternalTypes] [ExternalFuns] {T : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) (i : Input T) :=
  PV_RunJoin_NativeProjection55.observe PV_RunJoin_NativeCallback55.decode (execute store i)

def published [ExternalTypes] [ExternalFuns] {T : Type}
    (data : Phase → PV_RunJoin_OpeningImages54.Data) (plans : Phase → Plan)
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) (i : Input T) :=
  PV_RunJoin_NativeProjection55.observe id (modelExecute data plans store i)

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
    {T : Type} (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T) :
    PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
      (@actual (types base) (selected base heap box ops) T store)
      (@published (types base) (selected base heap box ops) T data plans store) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  intro i
  have callback := PV_RunJoin_NativeCallback55.complete base heap box ops data plans common backend finish query node ordering
  have transport := PV_RunJoin_NativeVariantTransport55.complete
    (fun proof pub => PV_RunJoin_NativeCallback55.decode proof=PV_RJ4IDB.PublicationInput.publish_compact pub)
    PV_RunJoin_NativeControl55.source (PV_RunJoin_NativeCallback55.model data plans)
    store i.public1 i.compiled .S2 callback i.hash i.context i.binding i.attempt i.store
  rw [← PV_RunJoin_NativeControlSource55.complete] at transport
  exact PV_RunJoin_NativeProjection55.complete PV_RunJoin_NativeCallback55.decode
    PV_RJ4IDB.PublicationInput.publish_compact _ _ transport
#print axioms Input
#print axioms execute
#print axioms modelExecute
#print axioms actual
#print axioms published
#print axioms complete
end R1Z.PV_RunJoin_NativePublication55
