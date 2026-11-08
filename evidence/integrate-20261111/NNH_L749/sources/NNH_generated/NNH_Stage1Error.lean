import NNE_RollbackView
import NNH_AcceptanceSig
set_option autoImplicit false
noncomputable section
namespace NNH_Stage1Error
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store Hist_RuntimeEntry CPP_BankState
open RSL RSL.TAS NNE_Observed

theorem error (S : Sig) (d : NNE_AcceptanceSig.Data S) (V : VLib)
 (P : PreparedNew V) (C : TX1_345.S1Lib V) (c : S.Ctx)
 (a1 : NND_A1 (NNH_AcceptanceSig.physical S d) V P C) (hx : S.Exhibited c)
 (before : Bank) (input : CPP_Invocation.Invocation Bool) (env : Env)
 (envrep : S.EnvRep c env) (post : SdkState) (es : List Event) (error : ProgramError)
 (route : Hiq_ReleaseRoute.stage1 input.call.data)
 (href : TX1_344.Ref V P C (args before input (d.program c)) (state before input) env
   ⟨.ret (.error error,post),es⟩)
 (hstate : input.call.state = true) :
 CPP_BankState.apply (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
   NNE_AbortIndicator.allocator (d.program c) before (.invoke input) = (before,.rollback) := by
 apply NNE_RollbackView.lift
 have rout : Hiq_ReleaseRoute.route (CPP_BankState.invocation before input).call.data = .first :=
   (Hiq_ReleaseRoute.first_iff _).mpr route
 simp only [CPP_Invocation.native,rout]
 by_cases count : input.count = 3
 · have href' : TX1_344.Ref V P C
     (NNE_EntryArgs.args (entry before input) 3 (d.program c) input.call.data)
     (NNE_Entry.state (entry before input) 0) env ⟨.ret (.error error,post),es⟩ := by
    simpa only [args,state,count] using href
   obtain ⟨es',hc⟩ := NNE_RslError.first V P C d.err d.invalid (entry before input)
     (d.program c) input.call.data env post error es route href'
   have noOk := (a1.stage1 c _ env _ _ hx envrep hc rfl
     (entry before input) (d.program c) input.call.data rfl).2 error rfl
   have noWrapper : ∀ saved post final,
    S2W_D189Wrappers.first (d.native1 (S.model1 c)) d.copy NNE_AbortIndicator.allocator
      (entry before input) (d.program c) input.call.data true ≠ ok (.Ok (saved,post,final)) := by
    intro saved post final called
    simp only [S2W_D189Wrappers.first,NNE_AbortIndicator.reserve_true,bind_tc_ok] at called
    cases hn : d.native1 (S.model1 c) (d.program c) (entry before input).first input.call.data with
    | fail e => simp only [hn,bind_tc_fail] at called; cases called
    | div => simp only [hn,bind_tc_div] at called; cases called
    | ok reply => cases reply with
     | Err e => simp only [hn,bind_tc_ok] at called; cases called
     | Ok value => exact noOk ⟨value,hn⟩
   apply NNE_AbortRollback.effect
   intro saved post final called
   apply noWrapper saved post final
   simpa only [CPP_Invocation.first,CPP_BankState.invocation,route,count,and_self,ite_true,hstate,entry]
    using called
 · exact NNE_Dispatch.first_wrong_count (d.native1 (S.model1 c)) d.copy NNE_AbortIndicator.allocator
     (d.program c) before.cells (CPP_BankState.invocation before input) count
#print axioms error
end NNH_Stage1Error
end
