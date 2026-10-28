import RPz7_PAln_OpeningStages
set_option autoImplicit false
namespace AspisR1.JGi_PrepareReturn
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem source {H : Type} (sem : r1_semantic.Verified H) (v : verifier.View)
    (gamma kappa a0 a1 claim : aspis_core.field.WideExact) (rho : aspis_core.field.QM31)
    (q : Array U32 22#usize) (t : transcript.Transcript H)
    (scratch : Array aspis_core.field.WideExact 29#usize) (variant : v.variant=.S2) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch (.Ok claim : core.result.Result aspis_core.field.WideExact verifier.Error)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue x =>
        ok (core.result.Result.Ok ({
          variant:=.S2,roots:=sem.roots,gamma:=gamma,kappa:=kappa,
          alpha:=Array.make 2#usize [a0,a1],rho:=rho,queries:=q,
          semantic_alpha:=sem.alpha,z:=sem.z,claim:=x,state:=t.state} : verifier.Prepared),scratch)
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual verifier.Prepared
          (core.convert.FromSame verifier.Error) residual
        ok (r,scratch))=
      ok (core.result.Result.Ok (PreparedScratchReachability.output sem v gamma kappa (Array.make 2#usize [a0,a1]) rho q claim t),scratch) := by
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,PreparedScratchReachability.output,variant]
#print axioms source
end AspisR1.JGi_PrepareReturn
