import NLJ_ObservedAll
import NLJ_ObservedFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Full source-fold/adopted-body equality, every result and ordered effect.
No native existence or native packet is inferred. -/
theorem exact_source {H : Type} (n : Nat) (s : State H) (enough : rank s ≤ n) :
 run (fold n s) = run (denote s) := by
 induction n generalizing s with
 | zero => have positive := rank_positive s;omega
 | succ n ih =>
   rw [←run_step s]
   change run (PreparedHashCode.bind (step s) _) = run (PreparedHashCode.bind (step s) continuation)
   rw [AuS1_Trace.run_bind,AuS1_Trace.run_bind]
   cases hs : run (step s) with
   | mk log reply =>
     cases reply with
     | fail e => rfl
     | div => rfl
     | ok post =>
       cases post with
       | inl out => rfl
       | inr after =>
         have smaller := decrease s after (congrArg Prod.snd hs)
         have room : rank after ≤ n := by omega
         have eq := ih after room
         simp only [AuS1_Trace.continueRun,continuation,eq]
#print axioms exact_source
#print exact_source
end AspisR1.NLJ_Observed
end
