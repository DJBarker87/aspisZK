import NBR_QueryConstruct
set_option autoImplicit false
namespace AspisR1.NBR_QueryTotal
open Aeneas Aeneas.Std Result AspisR1Query31Transcript NBA_QueryDriver

/-- The selected advance is in bounds on both accepted and rejected scans. -/
theorem finish (advances : Blocks) (index : Usize) (s : State) (bound : index.val<8) :
    ∃ out, finishAdvance advances index s=ok out := by
  by_cases accepted : s.accepted_len=aspis_core.r0_transcript.QUERY_COUNT
  · obtain ⟨next,call,value⟩ := WP.spec_imp_exists
      (Array.index_usize_spec advances index
        (by simpa only [Array.length,advances.property,show (8#usize).val=8 by rfl] using bound))
    exact ⟨.Ok (s.accepted,next),by
      simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,accepted,↓reduceIte,
        bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,call]⟩
  · exact ⟨.Err (.DrawLimitExhausted s.accepted_len aspis_core.r0_transcript.QUERY_MAX_DRAWS),by
      simp only [finishAdvance,aspis_core.r0_transcript.QueryScan.finish,accepted,↓reduceIte,
        bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]⟩

/-- Induction on first-stop traces, retaining rejection and proving that no
fail/div constructor arises from bounded advance selection. -/
theorem walk (advances : Blocks) (fallback : Usize) {pairs : NBL_QueryWalk.Pairs}
    {s : State} {result : Result Out}
    (trace : NBL_QueryWalk.Trace advances fallback pairs s result)
    (last : fallback.val<8) (indices : ∀ p∈pairs,p.2.val<8) :
    ∃ out,result=ok out := by
  induction trace with
  | exhausted s result call =>
    obtain ⟨out,h⟩ := finish advances fallback s last
    exact ⟨out,call.symm.trans h⟩
  | stopped block index rest s final words pending result decode scan stop call =>
    obtain ⟨out,h⟩ := finish advances index final (indices (block,index) (by simp))
    exact ⟨out,call.symm.trans h⟩
  | continuing block index rest s next words pending result decode scan stop tail ih =>
    exact ih (fun p hp => indices p (by simp only [List.mem_cons];exact Or.inr hp))

#print axioms finish
#print axioms walk
end AspisR1.NBR_QueryTotal
