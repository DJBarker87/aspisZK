import R1Z.PV_RunJoin_CodecComposition30
import R1Z.PV_RunJoin_OuterTransferDomain30
import R1Z.PV_RunJoin_OuterWithdrawalDomain30
import R1Z.PV_RunJoin_OuterTransferErrors30
import R1Z.PV_RunJoin_OuterWithdrawalErrors30
import R1Z.PV_RunJoin_DecodedDomain29
import R1Z.PV_RunJoin_DecodedArguments29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CodecOuter30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30
abbrev Snapshot := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev SnapshotError := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
abbrev decode := AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1

def snapshot (s : Snapshot) : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  snapshotFromForest (PV_RunJoin_DecodedArguments29.snapshot s)

inductive PreparationError (E : Type) where
  | snapshot : SnapshotError → PreparationError E
  | trace : E → PreparationError E

/-- Composition of the actual codec and a wrapper, retaining the decoder's
actual return. This definition asserts no deployment selector installation. -/
def run {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E)) :
    Result (Aeneas.Std.core.result.Result (Snapshot × C) (PreparationError E)) := do
  let r ← decode bytes
  match r with
  | .Err e => ok (.Err (.snapshot e))
  | .Ok s => do
    let r ← f (snapshot s)
    match r with
    | .Err e => ok (.Err (.trace e))
    | .Ok c => ok (.Ok (s,c))

theorem returned {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E))
    (s : Snapshot) (c : C) (h : run bytes f = ok (.Ok (s,c))) :
    decode bytes = ok (.Ok s) ∧ f (snapshot s) = ok (.Ok c) := by
  unfold run at h
  pv_peel h with decoded hd
  cases decoded with
  | Err e => cases h
  | Ok original =>
    pv_peel h with compiled hc
    cases compiled with
    | Err e => cases h
    | Ok result =>
      cases Result.ok.inj h
      exact ⟨hd,hc⟩
#print axioms returned

theorem success_iff {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E))
    (post : Snapshot → Prop)
    (hf : ∀ s, (∃ c, f (snapshot s) = ok (.Ok c)) ↔ post s) :
    (∃ output, run bytes f = ok (.Ok output)) ↔ PV_RunJoin_CodecComposition30.Path bytes post := by
  constructor
  · rintro ⟨⟨s,c⟩,h⟩
    obtain ⟨hd,hc⟩ := returned bytes f s c h
    exact (PV_RunJoin_CodecComposition30.source_iff bytes post).mp ⟨s,hd,(hf s).mp ⟨c,hc⟩⟩
  · intro h
    obtain ⟨s,hd,hp⟩ := (PV_RunJoin_CodecComposition30.source_iff bytes post).mpr h
    obtain ⟨c,hc⟩ := (hf s).mpr hp
    refine ⟨(s,c),?_⟩
    unfold run
    rw [hd]
    simp only [bind_tc_ok]
    rw [hc]
    rfl
#print axioms success_iff

theorem snapshot_domain {C E : Type} (bytes : Slice U8)
    (f : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 → Result (Aeneas.Std.core.result.Result C E))
    (s : Snapshot) (c : C) (h : run bytes f = ok (.Ok (s,c))) :
    PV_RunJoin_SnapshotDomain29.Domain s :=
  PV_RunJoin_DecodedDomain29.domain bytes s (returned bytes f s c h).1
#print axioms snapshot_domain

variable [LaneRoot] [R1Z.BuilderForestAdmissionPort.ExternalLinear] [R1Z.BuilderForestAdmissionPort.Records]

theorem transfer_domain (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestPrivateTransferWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    (∃ output, run bytes (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_private_transfer_merged_c1_v1 p w context) = ok (.Ok output)) ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun s =>
      PV_RunJoin_OuterTransferDomain30.Path p w context (snapshot s)) :=
  success_iff bytes _ _ (fun s => PV_RunJoin_OuterTransferDomain30.success_iff p w context (snapshot s))
#print axioms transfer_domain

theorem withdrawal_domain (bytes : Slice U8)
    (p : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (w : pool_v1.pair_forest_trace.PoolV1PairForestWithdrawalWitnessV1)
    (context : pool_v1.payment_relation.PoolV1PaymentRelationContextV1) :
    (∃ output, run bytes (pool_v1.pair_forest_trace.compile_pool_v1_pair_forest_withdrawal_merged_c1_v1 p w context) = ok (.Ok output)) ↔
    PV_RunJoin_CodecComposition30.Path bytes (fun s =>
      PV_RunJoin_OuterWithdrawalDomain30.Path p w context (snapshot s)) :=
  success_iff bytes _ _ (fun s => PV_RunJoin_OuterWithdrawalDomain30.success_iff p w context (snapshot s))
#print axioms withdrawal_domain
end R1Z.PV_RunJoin_CodecOuter30
