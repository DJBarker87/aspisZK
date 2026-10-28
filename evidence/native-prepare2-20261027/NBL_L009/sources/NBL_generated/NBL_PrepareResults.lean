import NBL_PrepareControl
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareResults
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NBL_PrepareControl
open PreparedScratchReachability

/-- Query rejection exits before rho/powers/claim and preserves old scratch. -/
theorem query_error (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old : Scratch) (o : Opening H)
    (e : verifier.Error) (after : transcript.Transcript H)
    (call : B.sampling.queries D o.transcript o.row v.final_message=ok (.Err e,after)) :
    continuation B D sem v old o=ok (.Err e,old) := by
  simp only [continuation,call,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  rfl

/-- A claim rejection occurs AFTER scratch overwrite. The exact error is
returned with the produced powers; old scratch is not silently restored. -/
theorem claim_error (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (old g : Scratch) (o : Opening H)
    (queries : Array U32 22#usize) (t1 t2 : transcript.Transcript H) (row : U8)
    (rho : aspis_core.field.QM31) (e : verifier.Error)
    (qc : B.sampling.queries D o.transcript o.row v.final_message=ok (.Ok queries,t1))
    (nextRow : (o.row+1#u8 : Result U8)=ok row)
    (rc : PreparedModel.scalar_k B.sampling D t1 row emptyPayload=ok (rho,t2))
    (pc : B.powers 29#usize o.gamma=ok g)
    (cc : B.claim D sem v.y1 v.inactive g o.kappa=ok (.Err e)) :
    continuation B D sem v old o=ok (.Err e,g) := by
  simp only [continuation,qc,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    nextRow,lift]
  change (do
    let (r,t) ← PreparedModel.scalar_k B.sampling D t1 row emptyPayload
    let scratch ← B.powers 29#usize o.gamma
    let result ← B.claim D sem v.y1 v.inactive scratch o.kappa
    let cf ← core.result.Result.Insts.CoreOpsTry.branch result
    match cf with
    | .Continue claim => ok (core.result.Result.Ok (output sem v o.gamma o.kappa o.alpha r queries claim t),scratch)
    | .Break residual => do
      let error ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        verifier.Prepared (core.convert.FromSame verifier.Error) residual
      ok (error,scratch))=ok (.Err e,g)
  simp only [rc,pc,cc,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
  rfl

/-- Whole cohort query rejection from a linked opening, without a selected
whole-prepare result hypothesis. Native opening association is separate. -/
theorem prepare_query_error (B : PreparedScratchModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (old : Scratch) (o : Opening H)
    (e : verifier.Error) (after : transcript.Transcript H)
    (opened : opening B D sem v hash=ok o)
    (call : B.sampling.queries D o.transcript o.row v.final_message=ok (.Err e,after)) :
    PreparedScratchModel.prepare B D sem v hash old=ok (.Err e,old) := by
  rw [NBL_PrepareControl.source,run,opened,bind_tc_ok]
  exact query_error B D sem v old o e after call

#print axioms query_error
#print axioms claim_error
#print axioms prepare_query_error
end AspisR1.NBL_PrepareResults
end
