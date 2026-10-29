import PV_L1G_WorldRetry
set_option autoImplicit false
namespace PV_L1G_WorldRetry
open R1Z.PV_W_Threading
variable {W S P : Type}
/-- Full ordered leaf prefixes, complete Result and final successful world.
This equation is compositional, not an instance of native leaf adequacy. -/
theorem logged_join (a : Attempt W S P) (n k : Nat) (s : S) (w : W) :
 stateLog (run a n k s w) = PV_L1D_RetryFold.run (stateAttempt a) n k (w,s) := by
 induction n generalizing k s w with
 | zero => rfl
 | succ n ih =>
   cases h : (a k s w).outcome with
   | fail e => simp only [run,R1Z.PV_W_Threading.bind,h,stateLog,PV_L1D_RetryFold.run,stateAttempt,Bind.bind,Pure.pure,PV_L1D_Logged.pure,PV_L1D_Logged.bind]
   | div => simp only [run,R1Z.PV_W_Threading.bind,h,stateLog,PV_L1D_RetryFold.run,stateAttempt,Bind.bind,Pure.pure,PV_L1D_Logged.pure,PV_L1D_Logged.bind]
   | ok pair =>
     rcases pair with ⟨step,after⟩
     cases step with
     | done p => simp only [run,R1Z.PV_W_Threading.bind,h,lift,stateLog,PV_L1D_RetryFold.run,stateAttempt,Bind.bind,Pure.pure,PV_L1D_Logged.pure,PV_L1D_Logged.bind,List.append_nil]
     | stop e => simp only [run,R1Z.PV_W_Threading.bind,h,lift,stateLog,PV_L1D_RetryFold.run,stateAttempt,Bind.bind,Pure.pure,PV_L1D_Logged.pure,PV_L1D_Logged.bind,List.append_nil]
     | retry =>
       have rest := ih (k+1) after (a k s w).world
       simp only [run,R1Z.PV_W_Threading.bind,h,stateLog,PV_L1D_RetryFold.run,stateAttempt,Bind.bind,Pure.pure,PV_L1D_Logged.pure,PV_L1D_Logged.bind,List.map_append]
       cases tail : run a n (k+1) after (a k s w).world with
       | mk outcome world calls =>
         simp only [tail,stateLog] at rest
         rw [← rest]
         rfl
#print axioms logged_join
end PV_L1G_WorldRetry
