import NLC_Progress
import NLC_FinishFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLC_Finish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run Log)
/-- Internal construction of the actual bounded SOURCE invocation, retaining
all returned errors and abort prefixes. No native observation is inferred. -/
theorem source_invocation {H : Type} (n : Nat) (s : State H) (enough : fuel s ≤ n) :
 ∃ out log events, Invocation n s out log events := by
 induction n generalizing s with
 | zero => have := fuel_positive s;omega
 | succ n ih =>
   cases head : run (step s) with
   | mk log reply =>
     cases reply with
     | ok post =>
       cases post with
       | inl out => exact ⟨ok out,log,[s.next],.returned head⟩
       | inr after =>
         have decrease : fuel s = fuel after + 1 := fuel_next s after (congrArg Prod.snd head)
         have room : fuel after ≤ n := by omega
         obtain ⟨out,suffix,events,tail⟩ := ih after room
         exact ⟨out,log ++ suffix,s.next :: events,.next head tail⟩
     | fail error => exact ⟨fail error,log,[s.next],.fail head⟩
     | div => exact ⟨div,log,[s.next],.div head⟩

/-- The conditional fold premise is discharged internally for this source
machine. Equality with the adopted finish body and native cut production are
separate, OPEN obligations; this is NOT a row root. -/
theorem bounded_source_fold {H : Type} (s : State H) :
 ∃ out log events, Invocation (fuel s) s out log events ∧ run (fold (fuel s) s) = (log,out) := by
 obtain ⟨out,log,events,cuts⟩ := source_invocation (fuel s) s (Nat.le_refl _)
 exact ⟨out,log,events,cuts,fold_from_steps cuts⟩
#print axioms source_invocation
#print axioms bounded_source_fold
#print bounded_source_fold
end AspisR1.NLC_Finish
end
