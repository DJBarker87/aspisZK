-- NNH-prefixed weak-Err adaptation of the corresponding NNE module.
import NNH_Stage1View
import NNH_Stage1Error
set_option autoImplicit false
noncomputable section
namespace NNH_InvocationView
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Store Hist_RuntimeEntry CPP_BankState S2W_ReturnedCheckpoint
open RSL RSL.TAS NNE_Observed

/-- Actual observation to CPP store/event, with G2 as the ONLY ASQ8 premise. -/
theorem invocation (S : Sig) (d : NNH_AcceptanceSig.Data S) (V : VLib)
 (P : PreparedNew V) (C : TX1_345.S1Lib V) (c : S.Ctx)
 (a1 : NND_A1 (NNH_AcceptanceSig.physical S d) V P C) (hx : S.Exhibited c)
 (f : TX2_213.Args → SdkState → Env → Observation)
 (stage1 : ∀ a s env, TX2_221.stage1Route a.data = true → TX1_344.Ref V P C a s env (f a s env))
 (g2 : ∀ a s env, ASQ8 a.data → Frame s (f a s env))
 (reject : ∀ a s env, TX2_221.admitted a.data = false →
   f a s env = ⟨.ret (.error .invalidInstructionData,s),[]⟩)
 (before after : Bank) (input : CPP_Invocation.Invocation Bool) (env : Env)
 (envrep : S.EnvRep c env) (event : S2X.AccountEvent)
 (rep : Assoc before after input (f (args before input (d.program c)) (state before input) env) event) :
 CPP_BankState.apply (d.native1 (S.model1 c)) (d.native2 (S.model2 c)) d.copy
   NNE_AbortIndicator.allocator (d.program c) before (.invoke input) = (after,event) := by
 cases hr : Hiq_ReleaseRoute.route input.call.data with
 | first =>
  have route := (Hiq_ReleaseRoute.first_iff _).mp hr
  have rs : TX2_221.stage1Route (args before input (d.program c)).data = true :=
    (NNE_EntryArgs.stage1_test _).mpr route
  have href := stage1 _ (state before input) env rs
  generalize ho : f (args before input (d.program c)) (state before input) env = o at href rep
  cases o with
  | mk exit es =>
   cases exit with
   | abort =>
    have hb : input.call.state = false := rep.1
    obtain ⟨ha,he⟩ := rep.2
    subst after; subst event
    exact NNE_RollbackView.aborted _ _ d.copy (d.program c) before input route hb
   | diverge =>
    have hb : input.call.state = false := rep.1
    obtain ⟨ha,he⟩ := rep.2
    subst after; subst event
    exact NNE_RollbackView.aborted _ _ d.copy (d.program c) before input route hb
   | ret value =>
    rcases value with ⟨r,post⟩
    cases r with
    | ok unit =>
     cases unit
     exact NNH_Stage1View.success S d V P C c a1 hx before after input env envrep post es event route href rep
    | error pe =>
     have hb : input.call.state = true := rep.1
     obtain ⟨ha,he⟩ := rep.2
     subst after; subst event
     exact NNH_Stage1Error.error S d V P C c a1 hx before input env envrep post es pe route href hb
 | second =>
  have hq := ((Hiq_ReleaseRoute.second_iff _).mp hr).2
  have hq' : ASQ8 (args before input (d.program c)).data := (NNE_Route.asq8 _).mp hq
  exact NNE_RollbackView.asq8 _ _ d.copy (d.program c) before after input _ event rep (g2 _ _ env hq') hr
 | reject =>
  have hn := (Hiq_ReleaseRoute.reject_iff _).mp hr
  have h1 : ¬ (nativeBytes input.call.data = [3,10] ∨ nativeBytes input.call.data = [3,11]) :=
   fun h => hn.1 ((NNE_Route.stage1 _).mpr h)
  have h2 : (nativeBytes input.call.data).take 4 ≠ REQUEST_MAGIC :=
   fun h => hn.2 ((NNE_Route.asq8 _).mpr h)
  have hadm : TX2_221.admitted (args before input (d.program c)).data = false := by
   simp only [args,NNE_EntryArgs.args,TX2_221.admitted]
   simp [not_or.mp h1 |>.1,not_or.mp h1 |>.2,h2]
  rw [reject _ _ env hadm] at rep
  obtain ⟨ha,he⟩ := rep.2
  subst after; subst event
  apply NNE_RollbackView.lift
  exact NNE_Dispatch.rejected_view _ _ d.copy NNE_AbortIndicator.allocator (d.program c) before.cells
   (CPP_BankState.invocation before input) hr
#print axioms invocation
end NNH_InvocationView
end
