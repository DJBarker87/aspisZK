import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_QueryFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize

def boundaries : QueriesModel.Boundaries :=
  Query31ConcreteMaterializedSchedule.concreteBoundaries
    Query31ModelDriverChain.sourceDefaultState AspisS1M31Embedding.Total.embed

theorem installed {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    NBA_Installed.actual.sampling.queries D self row payload=
      QueriesModel.queries boundaries D self row payload := rfl

theorem factor (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    NBA_QueryFactor.queriesFactored B D self row payload=(do
      let after ← transcript.Transcript.absorb D self row payload
      let (blocks,advances) ← NBA_QueryFactor.materialize D after.hash after.state
      NBA_QueryFactor.finishQuery B D after blocks advances) := rfl

/-- Query rejection retains the absorbed state, after ALL eager digest pairs. -/
theorem error (B : QueriesModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (blocks advances : Blocks)
    (e : aspis_core.transcript.QuerySampleError)
    (decode : B.decode blocks advances=ok (.Err e)) :
    NBA_QueryFactor.finishQuery B D self blocks advances=ok (.Err .Transcript,self) := by
  simp only [NBA_QueryFactor.finishQuery,decode,bind_tc_ok,core.result.Result.map_err,
    transcript.Transcript.queries.closure.Insts.CoreOpsFunctionFnOnceTupleQuerySampleErrorError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
  rfl

/-- Every ghost embedding is instantiated and total; no 22 independent
successful embedding observations are supplied by the caller. -/
theorem success {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (blocks advances : Blocks)
    (q : Array U32 22#usize) (state : Bytes32)
    (decode : boundaries.decode blocks advances=ok (.Ok (q,state))) :
    NBA_QueryFactor.finishQuery boundaries D self blocks advances=
      ok (.Ok q,{self with state:=state}) := by
  obtain ⟨u0,r0,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 0#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u1,r1,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 1#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u2,r2,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 2#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u3,r3,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 3#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u4,r4,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 4#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u5,r5,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 5#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u6,r6,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 6#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u7,r7,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 7#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u8,r8,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 8#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u9,r9,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 9#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u10,r10,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 10#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u11,r11,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 11#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u12,r12,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 12#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u13,r13,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 13#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u14,r14,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 14#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u15,r15,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 15#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u16,r16,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 16#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u17,r17,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 17#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u18,r18,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 18#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u19,r19,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 19#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u20,r20,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 20#usize (by simp only [Array.length,q.property];decide))
  obtain ⟨u21,r21,_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q 21#usize (by simp only [Array.length,q.property];decide))
  simp only [NBA_QueryFactor.finishQuery,decode,bind_tc_ok,core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]
  simp only [boundaries,Query31ConcreteMaterializedSchedule.concreteBoundaries,
    r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,AspisS1M31Embedding.Total.embed_total,
    bind_tc_ok,trace.value]

#print axioms installed
#print axioms factor
#print axioms error
#print axioms success
end AspisR1.NBL_QueryFinish
end
