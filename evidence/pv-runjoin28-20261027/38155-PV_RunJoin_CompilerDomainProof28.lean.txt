import R1Z.PV_RunJoin_CompilerDomain28
import R1Z.PV_RunJoin_ControlDomain28
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerDomainProof28
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_ResultDomain28 PV_RunJoin_ControlDomain28

/-- Exact necessary AND sufficient domain for the extracted inner callee,
with no semantic admission, canonicality, or compiler success hypothesis. -/
theorem success_iff [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    (∃ compiled, pair_forest_trace.compile_forest_from_copies input out recipient
      change publicInput anchor snapshot = ok (.Ok compiled)) ↔
      PV_RunJoin_CompilerDomain28.Path input out recipient change publicInput anchor snapshot := by
  rw [success_wp]
  unfold pair_forest_trace.compile_forest_from_copies PV_RunJoin_CompilerDomain28.Path
  simp only [bind_wp,ite_wp,option_wp,flow_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp,Prod.exists]
#print axioms success_iff
end R1Z.PV_RunJoin_CompilerDomainProof28
