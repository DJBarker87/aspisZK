import NLR_PrepareFinalSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareComplete
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
open NLJ_Prepare
/-- The source interpreter itself produces its entered source prefix for
EVERY Result. It does not supply the missing physical native invocation. -/
theorem invocation (cfg : Configuration) {H : Type} (n : Nat) (s : State H)
 (enough : NLR_Prepare.rank s ≤ n) :
 ∃ events, Invocation cfg n s (run (fold cfg n s)).2 (run (fold cfg n s)).1 events := by
 induction n generalizing s with
 | zero => have positive := NLR_Prepare.rank_positive s;omega
 | succ n ih =>
  cases head : run (step cfg s) with
  | mk log result =>
   cases result with
   | fail e =>
    have actual : run (fold cfg (n+1) s)=(log,.fail e) := by
     change run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) _) = _
     rw [AuS1_Trace.run_bind,head]
     rfl
    rw [actual]
    exact ⟨[event s],.fail head⟩
   | div =>
    have actual : run (fold cfg (n+1) s)=(log,.div) := by
     change run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) _) = _
     rw [AuS1_Trace.run_bind,head]
     rfl
    rw [actual]
    exact ⟨[event s],.div head⟩
   | ok post =>
    cases post with
    | inl out =>
     have actual : run (fold cfg (n+1) s)=(log,.ok out) := by
      change run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) _) = _
      rw [AuS1_Trace.run_bind,head]
      change (log++[],ok out)=(log,ok out)
      rw [List.append_nil]
     rw [actual]
     exact ⟨[event s],.returned head⟩
    | inr after =>
     have smaller := NLR_Prepare.decrease cfg s after (congrArg Prod.snd head)
     have room : NLR_Prepare.rank after ≤ n := by omega
     obtain ⟨events,tail⟩ := ih after room
     have actual : run (fold cfg (n+1) s)=
      (log++(run (fold cfg n after)).1,(run (fold cfg n after)).2) := by
      change run (AspisR1PublicPreparation.PreparedHashCode.bind (step cfg s) _) = _
      rw [AuS1_Trace.run_bind,head]
      rfl
     rw [actual]
     exact ⟨event s::events,.next head tail⟩
#print axioms invocation
set_option pp.proofs false
#print invocation
end AspisR1.NLR_PrepareComplete
end
