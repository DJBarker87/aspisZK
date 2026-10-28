import PV_B3P_PrefixTypes224
import PV_B3P_ScheduleResult133
namespace PV_B3P_HelperRegistryGuard224
open Aeneas Aeneas.Std PV_B3P_224Prefix PV_B3P_Schedule133
set_option autoImplicit false

abbrev NativeLink := aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1
abbrev NativeError := aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1

def agrees (scheduled : Link) (candidate : NativeLink) : Prop :=
  candidate.producer.row.val = scheduled.producer ∧ candidate.consumer.row.val = scheduled.consumer
instance (scheduled : Link) (candidate : NativeLink) : Decidable (agrees scheduled candidate) := by
  unfold agrees
  infer_instance

def check (scheduled : Link) (candidate : NativeLink) : Result (core.result.Result NativeLink NativeError) :=
  if agrees scheduled candidate then .ok (.Ok candidate) else .ok (.Err .CopyLayout)

theorem success (scheduled : Link) (candidate output : NativeLink)
    (h : check scheduled candidate = .ok (.Ok output)) :
    output = candidate ∧ agrees scheduled output := by
  unfold check at h
  split at h <;> simp_all

theorem bounded (scheduled : Link) (hs : scheduled ∈ forestLinks legacyLinks)
    (candidate output : NativeLink) (h : check scheduled candidate = .ok (.Ok output)) :
    output.producer.row.val < 1024 ∧ output.consumer.row.val < 1024 := by
  have hm := (success scheduled candidate output h).2
  have hb := PV_B3P_ScheduleResult133.all_endpoints_in_bounds scheduled hs
  unfold agrees at hm
  omega

#print axioms success
#print axioms bounded
end PV_B3P_HelperRegistryGuard224
