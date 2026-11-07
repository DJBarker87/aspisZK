import NLU_StepProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Source-side value/log projection of the linear-owner interpreter. Does
not establish any physical ownership or native parent cut. -/
theorem fold_projection {H : Type} (n : Nat) (s : NLU.State H) :
 (digestLog (fold n s).events,eraseReply (fold n s).reply)=
 run (NLC_Finish.fold n s.machine) := by
 induction n generalizing s with
 | zero => rfl
 | succ n ih =>
   change _=run (PreparedHashCode.bind (NLC_Finish.step s.machine) (fun post =>
    match post with | .inl out => pure out | .inr after => NLC_Finish.fold n after))
   rw [AuS1_Trace.run_bind]
   cases h : run (NLC_Finish.step s.machine) with
   | mk log reply =>
     cases reply with
     | fail err =>
       simp only [fold,step,h,AuS1_Trace.continueRun,eraseReply,bind_tc_fail,
        digest_append,entered_digest,map_digest,List.nil_append]
     | div =>
       simp only [fold,step,h,AuS1_Trace.continueRun,eraseReply,bind_tc_div,
        digest_append,entered_digest,map_digest,List.nil_append]
     | ok post =>
       cases post with
       | inl out =>
         cases out with
         | Ok value =>
           simp only [fold,step,h,carry,AuS1_Trace.continueRun,eraseReply,bind_tc_ok,
            digest_append,entered_digest,map_digest,List.nil_append]
           rfl
         | Err err =>
           by_cases live : s.owner=.live
           all_goals simp only [fold,step,h,carry,live,ite_true,ite_false,AuS1_Trace.continueRun,
            eraseReply,bind_tc_ok,digest_append,entered_digest,map_digest,List.nil_append]
           all_goals rfl
       | inr after =>
         have next := ih (⟨after,carryOwner s⟩ : NLU.State H)
         have logs := congrArg Prod.fst next
         have values := congrArg Prod.snd next
         dsimp only at logs values
         simp only [fold,step,h,carry,AuS1_Trace.continueRun]
         rw [digest_append,digest_append,digest_append,entered_digest,map_digest]
         have noAcquire : digestLog (if s.machine.next=NLC_Finish.Event.claims then [NLU.Event.acquire] else [])=[] := by split <;> rfl
         rw [noAcquire,List.nil_append,List.append_nil,logs,values]
#print axioms fold_projection
set_option pp.proofs false in #print fold_projection
end AspisR1.NLU
end
