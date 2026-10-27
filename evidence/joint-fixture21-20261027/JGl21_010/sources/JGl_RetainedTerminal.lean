import JGl_TerminalSuccess
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_RetainedTerminal
open Aeneas Aeneas.Std Result FIq_Native

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (hash : H) :
    ∃ out, FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
      JFm_PartialAlpha.a10 JFm_Begin.challenges=ok (.Ok out) ∧ FIp_SemanticValues.Canon out := by
  obtain ⟨selected,a,b,c,m,s,sops,sem,pos,comp,g,h,copy,out,
    gather,hs,ha,hb,hc,hl,block,sel,ps,runpos,cpos,vpos,runsem,csem,vsem,runh,runcopy,
    runcomp,ccomp,cg,vcomp,run,cout,vout⟩ := JGl_TerminalSuccess.source D B hash
  refine ⟨FIq_Carriers.fromQ out,?_,cout⟩
  unfold FIq_Terminal.terminal
  change (do
    let r ← pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
      (FIq_Carriers.toPublic JFs_PublicSerialization.value) JFu_TerminalCallback.claims
      JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges
    match r with
    | .Ok q => ok (.Ok (FIq_Carriers.fromQ q))
    | .Err e => ok (.Err (FIq_Terminal.fromError e)))=ok (.Ok (FIq_Carriers.fromQ out))
  rw [run,bind_tc_ok]
#print axioms source
end AspisR1.JGl_RetainedTerminal
end
