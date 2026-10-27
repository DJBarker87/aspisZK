import RPu_FIr_RootValue
import RPu_FJn_H1Index
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_H1Origin
open Aeneas Aeneas.Std Result FIq_Native
open FIr_TerminalTrace (NQ SemPub composition)

theorem reached (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (success : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize 26#usize=ok h := by
  unfold composition pool_v1.pair_forest_semantic_terminal.composition_parts at success
  obtain ⟨⟨amount,invalid⟩,amountCall,success⟩ := Port3_PushFrame.bind_success _ _ _ success
  cases invalid with
  | true => cases success
  | false =>
    obtain ⟨validated,validation,success⟩ := Port3_PushFrame.bind_success _ _ _ success
    cases validated with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at success
      cases success
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at success
      obtain ⟨a,ha,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨a1,ha1,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨a2,ha2,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨maskOnly,hm,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨selectors,hs,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨sops,hsp,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨poseidon,hp,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨semantic,hsem,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨column,hcol,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨h1,hh1,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨variant,hv,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨copy,hcopy,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨prepared,hprep,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨iterator,hi,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨reverse,hr,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨middle,hmid,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨iterator1,hi1,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨reverse1,hr1,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨final,hfinal,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨gColumn,hgc,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      obtain ⟨gValue,hg,success⟩ := Port3_PushFrame.bind_success _ _ _ success
      have output := core.result.Result.Ok.inj (Result.ok.inj success)
      have same : h1=h := congrArg (fun p : NQ × Array NQ 16#usize × Array NQ 10#usize × NQ × NQ × NQ=>p.2.2.2.2.1) output
      have columnSame : column=26#usize := Result.ok.inj (hcol.symm.trans FJn_H1Index.value)
      rw [←same,←columnSame]
      exact hh1

#print axioms reached
end AspisR1.FJn_H1Origin
end
