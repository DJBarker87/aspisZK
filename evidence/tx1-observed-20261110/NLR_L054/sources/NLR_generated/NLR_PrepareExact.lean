import NLR_PrepareAll
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_Prepare
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open NLJ_Prepare
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Full source-fold/adopted-body equality, every result and ordered effect.
No native existence or native packet is inferred. -/
theorem exact_source (cfg : Configuration) {H : Type} (n : Nat) (s : State H) (enough : rank s ≤ n) :
 run (fold cfg n s) = run (denote cfg s) := by
 induction n generalizing s with
 | zero => have positive := rank_positive s;omega
 | succ n ih =>
   rw [←source_run cfg s]
   change run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) _) = run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) (continuation cfg))
   rw [AspisR1.AuS1_Trace.run_bind,AspisR1.AuS1_Trace.run_bind]
   cases hs : run (step cfg s) with
   | mk log reply =>
     cases reply with
     | fail e => rfl
     | div => rfl
     | ok post =>
       cases post with
       | inl out => rfl
       | inr after =>
         have smaller := decrease cfg s after (congrArg Prod.snd hs)
         have room : rank after ≤ n := by omega
         have eq := ih after room
         simp only [AspisR1.AuS1_Trace.continueRun,continuation,eq]
#print axioms exact_source
set_option pp.proofs false
#print exact_source
end AspisR1.NLR_Prepare
end
