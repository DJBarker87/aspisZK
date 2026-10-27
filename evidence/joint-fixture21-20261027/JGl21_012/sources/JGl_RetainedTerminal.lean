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
  dsimp only [JFu_TerminalCallback.claims,JFu_TerminalPrefix.alpha,JFu_TerminalPrefix.challenges] at run
  rw [run,bind_tc_ok]
#print axioms source
end AspisR1.JGl_RetainedTerminal
end
