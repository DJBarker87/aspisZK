from pathlib import Path
root=Path(__file__).resolve().parents[2]
s=(root/'lean/NBL_PrepareTrace.lean').read_text()
start=s.index('theorem success')
end=s.index('\n#print axioms query_error')
s=s[start:end].replace('theorem success','theorem source',1)
a=s.index('      PreparedScratchModel.prepare')
b=s.index(' := by',a)
s=s[:a]+'''      PreparedHashCode.run (NBL_CohortCode.code D sem
        (AspisR1SelectedWideViewV1.preparedView view) hash old)=
        (NBL_HashReplay.events D hash
          (opening.log++NBL_QueryHashReplay.log queries++rhoBlock.log),
        ok (.Ok (output sem (AspisR1SelectedWideViewV1.preparedView view)
          opening.gamma.value opening.kappa.value opening.output.alpha rho q
          (NBA_ClaimCallee.wide claim) rhoBlock.after),mapArray NBA_ClaimCallee.wide g))'''+s[b:]
a=s.index('  refine ⟨g,claim,native,trace,canonical,?_⟩')
s=s[:a]+'''  refine ⟨g,claim,native,trace,canonical,?_⟩
  let C := preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries
  have queryRun := NBL_QueryHashReplay.source D opening.alpha1.block.after 31#u8 view.final_message queries
  rw [selected] at queryRun
  have rhoRun := NBL_ScalarHashReplay.rho D {queries.afterAbsorb with state:=state}
    32#u8 emptyPayload rhoBlock digits last rho division packed
  have powerRun : PreparedHashCode.run (C.powers 29#usize opening.output.gamma)=
      ([],ok (mapArray NBA_ClaimCallee.wide g)) := by
    change PreparedHashCode.run (monadLift (NBA_Installed.actual.powers 29#usize opening.gamma.value) : PreparedHashCode.Code _)=_
    rw [NBL_CodeRunLaws.lift_run,powers]
  have claimRun : PreparedHashCode.run (C.claim D sem view.y1
      (AspisR1SelectedWideViewV1.preparedView view).inactive
      (mapArray NBA_ClaimCallee.wide g) opening.output.kappa)=
      ([],ok (.Ok (NBA_ClaimCallee.wide claim))) := by
    change PreparedHashCode.run (monadLift (NBA_Installed.actual.claim D sem view.y1
      (AspisR1SelectedWideViewV1.preparedView view).inactive
      (mapArray NBA_ClaimCallee.wide g) opening.kappa.value) : PreparedHashCode.Code _)=_
    rw [NBL_CodeRunLaws.lift_run,claimed]
  have tail := NBL_ContinuationHash.tail C D sem
    (AspisR1SelectedWideViewV1.preparedView view) old
    (mapArray NBA_ClaimCallee.wide g) opening.output
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries))
    (NBL_HashReplay.events D hash rhoBlock.log)
    q {queries.afterAbsorb with state:=state} rhoBlock.after 32#u8 rho
    (.Ok (NBA_ClaimCallee.wide claim)) queryRun row rhoRun powerRun claimRun
  have whole := NBL_ContinuationHash.after_opening C D sem
    (AspisR1SelectedWideViewV1.preparedView view) hash old opening.output
    (NBL_HashReplay.events D hash opening.log)
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries)++
      NBL_HashReplay.events D hash rhoBlock.log) _
    (NBL_OpeningHashReplay.source D sem _ hash opening) tail
  simpa only [C,NBL_CohortCode.code,NBL_OpeningTrace.Trace.output,NBL_HashReplay.events,List.map_append,List.append_assoc] using whole
'''
pre='''import NBL_PrepareTrace
import NBL_ContinuationHash
import NBL_OpeningHashReplay
import NBL_QueryHashReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareHashTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability PreparedHashCode
/-- Exact existing cohort preparation code: one chronological trace, full
Prepared value, final scratch and every attempted digest. Native construction
of the local producing executions remains a separate obligation. -/
'''
(root/'lean/NBL_PrepareHashTrace.lean').write_text(pre+s+'\n#print axioms source\nend AspisR1.NBL_PrepareHashTrace\nend\n')
