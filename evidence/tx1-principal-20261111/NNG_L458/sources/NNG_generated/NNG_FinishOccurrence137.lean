import NNG_FinishInput137
import NNG_Producer137
import NNG_Candidate136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FinishOccurrence137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport NMT_CallTree NNG_Observed136

theorem run_invoke {Args A : Type} (site : String) (args : Args) (reply : Result A) :
    run (invoke site args reply)=(reply,[NMT_CallTree.Event.call site args reply]) := by
  cases reply <;> rfl
#print axioms run_invoke

theorem observation (a : NNG_Data137.Args) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : RSL.Observer)
    (fallback : NNG_Data137.fallback a env=c.eta) :
    NNG_Observed136.observation (NNG_Output137.decode a env) (NNG_Events137.events env)
      (NNG_Tree137.finish (NNG_Context137.calls env) (NNG_Context137.input a obs env)
        (fromT13 (LIB_VCarriers.prefixRaw p)) (fromT10 t) (fromT3 (LIB_VCarriers.challengesRaw c))) =
      NNG_Producer136.producer ⟨a.public_,p,t,c⟩ obs env := by
  unfold NNG_Tree137.finish NNG_Observed136.observation
  simp only [run_invoke,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [NNG_Events137.finish_call]
  unfold NNG_Producer136.producer NNG_DEnvObserved136.producer NNG_Observed136.producer
  simp only [NNG_Context137.calls,NNG_Context137.input,NNG_FinishAdapter137.call,
    NMP_Finish136Transport.adapt,NNG_FinishAdapter137.oldFinish,fromT9_inverse,fromT13_inverse,
    fromT10_inverse,fromT3_inverse,NNG_Events137.finish,NNG_FinishInput137.input]
  dsimp only [NNG_Representation136.calls]
  apply congrArg₂ RSL.Obs.mk
  · generalize NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env)
      (NNG_Representation136.input ⟨a.public_,p,t,c⟩ obs env) = r
    cases r with
    | fail e=>rfl
    | div=>rfl
    | ok r=>
      change RSL.Exit.ret _ = RSL.Exit.ret _
      apply congrArg RSL.Exit.ret
      cases r with
      | Ok v=>exact NNG_Output137.child_decode a env ⟨a.public_,p,t,c⟩ fallback (.Ok v)
      | Err e=>exact NNG_Output137.child_decode a env ⟨a.public_,p,t,c⟩ fallback (.Err e)
  · rfl
#print axioms observation

theorem occurrence (a : NNG_Data137.Args) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (t : LIB_VCarriers.Transcript) (c : LIB_VCarriers.Challenges) (obs : RSL.Observer)
    (domain : RSL.TX1_136.Domain LIB_VLib.library ⟨a.public_,p,t,c⟩)
    (fallback : NNG_Data137.fallback a env=c.eta) :
    RSL.Spec.call (RSL.TX1_136.Domain LIB_VLib.library) (RSL.TX1_136.Ref LIB_VLib.library) ⟨a.public_,p,t,c⟩ env
      (NNG_Observed136.observation (NNG_Output137.decode a env) (NNG_Events137.events env)
        (NNG_Tree137.finish (NNG_Context137.calls env) (NNG_Context137.input a obs env)
          (fromT13 (LIB_VCarriers.prefixRaw p)) (fromT10 t) (fromT3 (LIB_VCarriers.challengesRaw c)))) := by
  rw [observation a env p t c obs fallback]
  exact ⟨domain,NNG_Candidate136.candidate _ obs env domain⟩
#print axioms occurrence
end AspisR1.NNG_FinishOccurrence137
