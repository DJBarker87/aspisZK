from pathlib import Path
s='''import NBA_QueryJoin
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
'''
for i in range(22):
 s+=f'''  obtain ⟨u{i},r{i},_⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q {i}#usize (by simp only [Array.length,q.property];decide))
'''
s+='''  simp only [NBA_QueryFactor.finishQuery,decode,bind_tc_ok,core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]
  simp only [boundaries,Query31ConcreteMaterializedSchedule.concreteBoundaries,
    '''+','.join('r'+str(i) for i in range(22))+''',AspisS1M31Embedding.Total.embed_total,
    bind_tc_ok,trace.value]

#print axioms installed
#print axioms factor
#print axioms error
#print axioms success
end AspisR1.NBL_QueryFinish
end
'''
s=s.replace('Query31ModelDriverChain.sourceDefaultState','Query31ConcreteDriverTraceFacts.sourceDefaultState')
a=s.index('def boundaries');b=s.index('theorem factor')
dictionary=s[a:b].replace('D self row payload := rfl','D self row payload := by\n  rw [NBA_Scalars.sampling]\n  rfl')
dict_source='import NBA_Scalars\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.NBL_QueryDictionary\nopen Aeneas Aeneas.Std Result AspisR1PublicPreparation\ndef boundaries : QueriesModel.Boundaries :=\n  Query31ConcreteMaterializedSchedule.concreteBoundaries\n    Query31ConcreteDriverTraceFacts.sourceDefaultState AspisS1M31Embedding.Total.embed\n\ntheorem installed {H : Type} (D : aspis_core.Digest32 H)\n    (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :\n    NBA_Installed.actual.sampling.queries D self row payload=\n      QueriesModel.queries boundaries D self row payload := by\n  rw [NBA_Scalars.sampling]\n  simp only [AspisR1ClaimPreparedBridge.withCandidateSamplers,\n    AspisR1ClaimPreparedBridge.withCandidateGamma,\n    AspisR1Post25SamplerOrdinaryCallbackV2.withCandidateOrdinary,NBA_Scalars.base,\n    AspisR1PublicPreparation.PreparedFromQmSourceBridge.withSourceFromQm,\n    AspisR1ClaimPreparedBridge.CurrentQueryRho.withConcreteQueries,boundaries]\n\n\n#print axioms installed\nend AspisR1.NBL_QueryDictionary\nend\n'
s=s[:a]+s[b:]
s=s.replace('import NBA_QueryJoin','import NBA_QueryJoin\nimport NBL_QueryDictionary').replace('open Aeneas Aeneas.Std Result AspisR1PublicPreparation','open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_QueryDictionary').replace('#print axioms installed\n','').replace('trace.value]\n','trace.value,Aeneas.Std.uncurry]\n')
import sys
for name,source in [('NBL_QueryDictionary',dict_source),('NBL_QueryFinish',s)]:
 p=Path('lean')/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==source,name
 else:p.write_text(source)
