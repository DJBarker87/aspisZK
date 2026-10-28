import R1Z.PV_RunJoin_OuterFuns30
import R1Z.PV_RunJoin_CompilerDomainProof28
import R1Z.PV_RunJoin_RuntimeDomain30
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterCall30
open Aeneas Aeneas.Std Result
open PV_RunJoin_Outer30 R1Z.PV_RunJoin_OuterABI30

def mapped {α β ε ζ : Type} (f : α → β) (g : ε → ζ)
    (m : Result (Aeneas.Std.core.result.Result α ε)) :
    Result (Aeneas.Std.core.result.Result β ζ) := do
  let r ← m
  ok (match r with | .Ok a => .Ok (f a) | .Err e => .Err (g e))

theorem mapped_success_iff {α β ε ζ : Type} (f : α → β) (g : ε → ζ)
    (m : Result (Aeneas.Std.core.result.Result α ε)) :
    (∃ b, mapped f g m = ok (.Ok b)) ↔ ∃ a, m = ok (.Ok a) := by
  constructor
  · rintro ⟨b,h⟩
    unfold mapped at h
    pv_peel h with r hr
    cases r with
    | Ok a => exact ⟨a,hr⟩
    | Err e => cases h
  · rintro ⟨a,h⟩
    exact ⟨f a,by unfold mapped; rw [h]; rfl⟩
#print axioms mapped_success_iff

variable [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem inner_success_iff
    (input : pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (change : pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pool_v1.pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    (∃ c, pool_v1.pair_forest_trace.compile_forest_from_copies input out recipient
      change public1 anchor snapshot = ok (.Ok c)) ↔
    R1Z.PV_RunJoin_CompilerDomain28.Path (inputToForest input) out
      (recipient.map noteToForest) (noteToForest change) (publicToForest public1)
      anchor (snapshotToForest snapshot) := by
  change (∃ c, mapped compilationFromForest errorFromForest
    (R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.compile_forest_from_copies
      (inputToForest input) out (recipient.map noteToForest) (noteToForest change)
      (publicToForest public1) anchor (snapshotToForest snapshot)) = ok (.Ok c)) ↔ _
  rw [mapped_success_iff,PV_RunJoin_CompilerDomainProof28.success_iff]
#print axioms inner_success_iff

theorem inner_return
    (input : pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (change : pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pool_v1.pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (c : pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pool_v1.pair_forest_trace.compile_forest_from_copies input out recipient
      change public1 anchor snapshot = ok (.Ok c)) :
    R1Z.BuilderForestAdmissionPort.pool_v1.pair_forest_trace.compile_forest_from_copies
      (inputToForest input) out (recipient.map noteToForest) (noteToForest change)
      (publicToForest public1) anchor (snapshotToForest snapshot) = ok (.Ok (compilationToForest c)) := by
  unfold pool_v1.pair_forest_trace.compile_forest_from_copies at h
  pv_peel h with r hr
  cases r with
  | Ok original =>
    cases Result.ok.inj h
    rw [compilation_roundtrip]
    exact hr
  | Err e => cases h
#print axioms inner_return

theorem runtime_success_iff
    (pool domain : Array U8 32#usize) (seq : U64) (anchor nullifier : Array U32 8#usize)
    (asset : U32) (input : pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    (∃ u, pool_v1.pair_trace.validate_common pool domain seq anchor nullifier asset
      input context = ok (.Ok u)) ↔
    PV_RunJoin_RuntimeDomain30.Path pool domain seq anchor nullifier asset
      (pairToAdmission input) (contextToAdmission context) := by
  change (∃ u, mapped id errorFromAdmission
    (AspisBuilderAdmissionSource.pool_v1.pair_trace.validate_common
      pool domain seq anchor nullifier asset (pairToAdmission input)
      (contextToAdmission context)) = ok (.Ok u)) ↔ _
  rw [mapped_success_iff,PV_RunJoin_RuntimeDomain30.success_iff]
#print axioms runtime_success_iff
end R1Z.PV_RunJoin_OuterCall30
