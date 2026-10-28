import R1Z.PV_RunJoin_HonestIdentification26
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PreparedPayload28
open Aeneas Aeneas.Std Result PV_Src_NativeInput
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
local notation "E" => PV_RunJoin_ShippedExternal.E_shipped
local notation "R" => PV_RunJoin_UniversalRecords22.shipped

/-- Inputs of the extracted inner compiler, with no cached output field. -/
structure Arguments where
  request : Request
  witness : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
  change : payment_relation.PoolV1OutputNoteWitnessV1
  laneAnchor : Array U32 8#usize
  snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1

def install (a : Arguments)
    (c : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) : Input :=
  ⟨a.request,a.witness,a.change,a.laneAnchor,a.snapshot,c⟩

def call (a : Arguments) := @pair_forest_trace.compile_forest_from_copies E R
  a.witness (outputValue a.request) (recipient a.request) a.change
  (forestPublic a.request) a.laneAnchor a.snapshot

/-- Proof-local packaging of the compiler's actual return. This adds no
validation and is not substituted for either Rust preparation wrapper. -/
def package (a : Arguments) : Result (core.result.Result Input pair_trace.PoolV1PairTraceErrorV1) := do
  let result ← call a
  match result with
  | .Ok c => ok (.Ok (install a c))
  | .Err e => ok (.Err e)

/-- Successful packaging fixes the complete returned payload and both Result
layers. Admission and representation validity are not inferred here. -/
theorem cached_return (a : Arguments) (i : Input)
    (h : package a = ok (.Ok i)) :
    @run E R i = ok (.Ok i.compiled) := by
  unfold package at h
  pv_peel h with result hr
  cases result with
  | Ok c =>
    cases Result.ok.inj h
    exact hr
  | Err e => cases h
#print axioms cached_return

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exact remaining obligations after actual successful output packaging;
none is hidden in the payload type or equated with SourceIdentification. -/
theorem honest_iff (a : Arguments) (i : Input)
    (h : package a = ok (.Ok i)) :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i ↔
      PV_RunJoin_UniversalBuild22.Admission (K := K) i ∧
      PV_Src_RecordReference.Checked i ∧
      ∀ l : Fin 20, R0Z.WriterRefine.Canon8 i.snapshot.frontier.val[l.val]! := by
  constructor
  · exact fun hi => ⟨hi.1,hi.2.2⟩
  · exact fun hi => ⟨hi.1,cached_return a i h,hi.2⟩
#print axioms honest_iff
end R1Z.PV_RunJoin_PreparedPayload28
