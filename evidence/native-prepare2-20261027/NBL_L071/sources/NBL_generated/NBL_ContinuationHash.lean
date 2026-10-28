import NBL_EffectControl
import NBL_CodeRunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_ContinuationHash
open Aeneas Aeneas.Std Result AspisR1PublicPreparation PreparedHashCode NBL_CodeRunLaws
open NBL_PrepareControl PreparedScratchReachability

theorem query_error (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H)
    (log : Log) (e : verifier.Error) (after : transcript.Transcript H)
    (qc : run (B.queries D o.transcript o.row v.final_message)=(log,ok (.Err e,after))) :
    run (NBL_EffectControl.continuation B D sem v old o)=(log,ok (.Err e,old)) := by
  simp only [NBL_EffectControl.continuation,bind_run,qc,chain,lift_run,pure_run,lift,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,List.append_nil,List.nil_append]

/-- Exact scratch effect for BOTH claim Results. Local callback logs and
results are joined, not replaced by a whole-prepare equality premise. -/
theorem tail (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old g : Scratch) (o : Opening H)
    (queryLog rhoLog : Log) (q : Array U32 22#usize) (t1 t2 : transcript.Transcript H)
    (row : U8) (rho : aspis_core.field.QM31)
    (claimResult : core.result.Result aspis_core.field.WideExact verifier.Error)
    (qc : run (B.queries D o.transcript o.row v.final_message)=(queryLog,ok (.Ok q,t1)))
    (nextRow : (o.row+1#u8 : Result U8)=ok row)
    (rc : run (B.rho D t1 row emptyPayload)=(rhoLog,ok (rho,t2)))
    (pc : run (B.powers 29#usize o.gamma)=([],ok g))
    (cc : run (B.claim D sem v.y1 v.inactive g o.kappa)=([],ok claimResult)) :
    run (NBL_EffectControl.continuation B D sem v old o)=
      (queryLog++rhoLog,ok (match claimResult with
        | .Ok claim => (.Ok (output sem v o.gamma o.kappa o.alpha rho q claim t2),g)
        | .Err e => (.Err e,g))) := by
  cases claimResult <;>
    simp only [NBL_EffectControl.continuation,bind_run,qc,chain,lift_run,pure_run,lift,
      core.result.Result.Insts.CoreOpsTry.branch,nextRow,rc,pc,cc,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame,List.append_nil,List.nil_append]

theorem after_opening (B : PreparedSourceEffects.Effects Code) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) (o : Opening H)
    (openingLog tailLog : Log) (result : Result Out)
    (opened : run (NBL_EffectControl.opening B D sem v hash)=(openingLog,ok o))
    (continued : run (NBL_EffectControl.continuation B D sem v old o)=(tailLog,result)) :
    run (PreparedSourceEffects.prepare B D sem v hash old)=(openingLog++tailLog,result) := by
  rw [NBL_EffectControl.source]
  simp only [NBL_EffectControl.program,bind_run,opened,chain,continued]

#print axioms query_error
#print axioms tail
#print axioms after_opening
end AspisR1.NBL_ContinuationHash
end
