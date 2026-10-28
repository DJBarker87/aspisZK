import R1Z.PV_RunJoin_DecodedArguments29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_DecodedPackage29
open Aeneas Aeneas.Std Result R0Z.WriterRefine PV_Src_NativeInput
open PV_RunJoin_PreparedPayload28

theorem frontier (a : Arguments) (bytes : Slice U8)
    (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
      bytes = ok (.Ok s)) (i : Input)
    (h : package (PV_RunJoin_DecodedArguments29.arguments a s) = ok (.Ok i)) :
    ∀ l : Fin 20, Canon8 i.snapshot.frontier.val[l.val]! := by
  unfold package at h
  pv_peel h with result hr
  cases result with
  | Ok c =>
    cases Result.ok.inj h
    exact PV_RunJoin_DecodedArguments29.frontier bytes s decoded a c
  | Err e => cases h
#print axioms frontier

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Exact residual obligations after actual decoding and fresh inner-output
packaging. This is not a substitute for either native outer wrapper. -/
theorem honest_iff (a : Arguments) (bytes : Slice U8)
    (s : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1
      bytes = ok (.Ok s)) (i : Input)
    (h : package (PV_RunJoin_DecodedArguments29.arguments a s) = ok (.Ok i)) :
    PV_RunJoin_ConsumerBoundary25.HonestInput (K := K) i ↔
      PV_RunJoin_UniversalBuild22.Admission (K := K) i ∧ PV_Src_RecordReference.Checked i := by
  constructor
  · exact fun hi => ⟨hi.1,hi.2.2.1⟩
  · rintro ⟨admitted,checked⟩
    exact ⟨admitted,cached_return _ i h,checked,frontier a bytes s decoded i h⟩
#print axioms honest_iff
end R1Z.PV_RunJoin_DecodedPackage29
