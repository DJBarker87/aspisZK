import R1Z.PV_RunJoin_OuterCall30
import R1Z.PV_RunJoin_OuterABILaws30
import R1Z.PV_RunJoin_RejectionProof28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OuterInnerPath30
open Aeneas Aeneas.Std Result PV_RunJoin_Outer30
open PV_RunJoin_OuterABI30 PV_RunJoin_OuterABILaws30
open PV_RunJoin_ResultDomain28
variable [BuilderForestAdmissionPort.ExternalLinear] [BuilderForestAdmissionPort.Records]

variable (input : pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (change : pool_v1.payment_relation.PoolV1OutputNoteWitnessV1)
    (public1 : pool_v1.pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)

def Path : Prop := PV_RunJoin_CompilerDomain28.Path (inputToForest input) out
  (recipient.map noteToForest) (noteToForest change) (publicToForest public1) anchor (snapshotToForest snapshot)

def ErrorPath (e : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) : Prop :=
  PV_RunJoin_CompilerRejections28.Path (inputToForest input) out
    (recipient.map noteToForest) (noteToForest change) (publicToForest public1) anchor
    (snapshotToForest snapshot) (errorToForest e)

theorem inner_wp :
    wp (pool_v1.pair_forest_trace.compile_forest_from_copies input out recipient change
      public1 anchor snapshot) isRustOk ↔ Path input out recipient change public1 anchor snapshot :=
  (success_wp _).symm.trans (PV_RunJoin_OuterCall30.inner_success_iff _ _ _ _ _ _ _)
#print axioms inner_wp

theorem error_iff (e : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) :
    pool_v1.pair_forest_trace.compile_forest_from_copies input out recipient change
      public1 anchor snapshot = ok (.Err e) ↔
    ErrorPath input out recipient change public1 anchor snapshot e := by
  constructor
  · intro h
    unfold pool_v1.pair_forest_trace.compile_forest_from_copies at h
    pv_peel h with r hr
    cases r with
    | Ok c => cases h
    | Err native =>
      have he := Aeneas.Std.core.result.Result.Err.inj (Result.ok.inj h)
      have he' : native=errorToForest e := by
        simpa only [error_roundtrip] using congrArg errorToForest he
      apply (PV_RunJoin_RejectionProof28.error_iff _ _ _ _ _ _ _ _).mp
      rw [← he']
      exact hr
  · intro h
    have he := (PV_RunJoin_RejectionProof28.error_iff _ _ _ _ _ _ _ _).mpr h
    unfold pool_v1.pair_forest_trace.compile_forest_from_copies
    rw [he]
    simp only [bind_tc_ok,error_reverse]
#print axioms error_iff

theorem error_wp (e : pool_v1.pair_trace.PV30_PoolV1PairTraceErrorV1) :
    wp (pool_v1.pair_forest_trace.compile_forest_from_copies input out recipient change
      public1 anchor snapshot) (fun r => r = .Err e) ↔
    ErrorPath input out recipient change public1 anchor snapshot e :=
  (PV_RunJoin_RejectionProof28.eq_wp _ _).symm.trans (error_iff _ _ _ _ _ _ _ e)
#print axioms error_wp
end R1Z.PV_RunJoin_OuterInnerPath30
