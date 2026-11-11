import NLJ_ObservedExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Observed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run Log)
def initial {H : Type} (i : Input H) : State H := ⟨i,.parse⟩
theorem source_invocation {H : Type} (n : Nat) (s : State H) (enough : rank s ≤ n) :
 ∃ out log events, Invocation n s out log events := by
 induction n generalizing s with
 | zero => have positive := rank_positive s;omega
 | succ n ih =>
   cases hs : run (step s) with
   | mk log reply =>
     cases reply with
     | fail e => exact ⟨.fail e,log,[event s],.fail hs⟩
     | div => exact ⟨.div,log,[event s],.div hs⟩
     | ok post =>
       cases post with
       | inl out => exact ⟨.ok out,log,[event s],.returned hs⟩
       | inr after =>
         have smaller := decrease s after (congrArg Prod.snd hs)
         have room : rank after ≤ n := by omega
         obtain ⟨out,suffix,events,tail⟩ := ih after room
         exact ⟨out,log++suffix,event s::events,.next hs tail⟩

/-- Exact full source/adopted identity at the original arguments; no separate
body-success or endpoint premise appears. Native production remains OPEN. -/
theorem initial_source {H : Type} (i : Input H) :
 run (fold 6 (initial i)) =
 run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) :=
 exact_source 6 (initial i) (Nat.le_refl 6)

/-- NHZ-shaped conditional composition, now with source-order identification
PROVED internally. Its cuts still need the reviewed native producer. -/
theorem events_from_cuts {H : Type} (i : Input H) (out : Result (Out H))
 (log : Log) (events : List Event) (cuts : Invocation 6 (initial i) out log events) :
 run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (log,out) := by
 rw [←initial_source i]
 exact fold_from_steps cuts

/-- Existence is discharged for the source machine, not for native Rust. -/
theorem initial_fold {H : Type} (i : Input H) :
 ∃ out log events, Invocation 6 (initial i) out log events ∧
 run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (log,out) := by
 obtain ⟨out,log,events,cuts⟩ := source_invocation 6 (initial i) (Nat.le_refl 6)
 exact ⟨out,log,events,cuts,events_from_cuts i out log events cuts⟩
#print axioms source_invocation
#print axioms initial_source
#print axioms events_from_cuts
#print axioms initial_fold
#print events_from_cuts
end AspisR1.NLJ_Observed
end
