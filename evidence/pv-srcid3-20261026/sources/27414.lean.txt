import R1Z.BuilderForestAdmissionPort
import R1Z.PV_Src_Public

/-! Data at the actual extracted forest compiler/public-projection boundary.
The returned compilation is data; execution success is deliberately not part
of its definition or input carrier. Request variants fix the called output
value and optional recipient exactly as the two shipped entry wrappers do. -/
set_option autoImplicit false
namespace R1Z.PV_Src_NativeInput
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1

inductive Request where
  | transfer (publicInput : BuilderPublicProjection.Transfer)
      (recipient : payment_relation.PoolV1OutputNoteWitnessV1)
  | withdrawal (publicInput : BuilderPublicProjection.Withdrawal)

def forestPublic : Request → pair_forest_trace.ForestPublic
  | .transfer p _ => ⟨p.anchor_root,p.nullifier,some p.recipient_commitment,p.change_commitment,p.asset_id⟩
  | .withdrawal p => ⟨p.anchor_root,p.nullifier,none,p.change_commitment,p.asset_id⟩

def outputValue : Request → U32
  | .transfer _ r => r.value
  | .withdrawal p => p.amount

def recipient : Request → Option payment_relation.PoolV1OutputNoteWitnessV1
  | .transfer _ r => some r
  | .withdrawal _ => none

structure Input where
  request : Request
  witness : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
  change : payment_relation.PoolV1OutputNoteWitnessV1
  laneAnchor : Array U32 8#usize
  snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1
  compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1

/-- Actual extracted callee, including both native error layers. -/
def run [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]
    (i : Input) := pair_forest_trace.compile_forest_from_copies
  i.witness (outputValue i.request) (recipient i.request) i.change
  (forestPublic i.request) i.laneAnchor i.snapshot

/-- A field-preserving nominal adapter; there is no assumed transition or
public equality inside this definition. The transition comes from the actual
returned compiler payload, including both snapshot and afterstate. -/
def transition (t : pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    BuilderPublicProjection.Transition where
  live_snapshot := {
    pool := t.live_snapshot.pool
    deployment_domain := t.live_snapshot.deployment_domain
    sequence := t.live_snapshot.sequence
    next_pair_index := t.live_snapshot.next_pair_index
    current_root := t.live_snapshot.current_root
    frontier := t.live_snapshot.frontier }
  candidate_afterstate := {
    next_pair_index := t.candidate_afterstate.next_pair_index
    next_root := t.candidate_afterstate.next_root
    next_frontier := t.candidate_afterstate.next_frontier }

def publicInput (i : Input) : PV_Src_Public.Input :=
  match i.request with
  | .transfer p _ => .transfer p (transition i.compiled.public_statement)
  | .withdrawal p => .withdrawal p (transition i.compiled.public_statement)

def newRecords [BuilderForestAdmissionPort.Records] (i : Input) :=
  pair_forest_copy_builder.CopyRecords.new i.witness (outputValue i.request)
    (recipient i.request) i.change i.snapshot (forestPublic i.request).asset

/-- Pure projection of the actual returned merged columns. -/
def columns {K : Type} [Field K]
    (read : Array (alloc.vec.Vec U32) 16#usize → Fin 29 → Fin 1024 → U32)
    (out : Array (alloc.vec.Vec U32) 16#usize) : R0P.Trace K :=
  fun c r => R0Z.WriterRefine.liftU (read out c r)

#print axioms run
#print axioms transition
#print axioms publicInput
#print axioms newRecords
#print axioms columns
end R1Z.PV_Src_NativeInput
