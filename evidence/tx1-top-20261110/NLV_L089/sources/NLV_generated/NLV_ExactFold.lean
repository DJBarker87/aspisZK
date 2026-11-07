import NLV_All
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
/-- Full source continuation fold on the SAME state, including every early
Err and every outer fail/div. This does not manufacture native Cut admission. -/
theorem exact_source (cfg : Configuration)
 (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (n : Nat) (s : NLJ_Tx1.State) (enough : rank s≤n) (before : SdkC_Source.Log) :
 SdkC_Source.run h (fold cfg n s) before=SdkC_Source.run h (denote cfg s) before := by
 induction n generalizing s before with
 | zero => have hp:=positive s;omega
 | succ n ih =>
   rw [←source_step cfg s]
   change SdkC_Source.run h (CheckpointBytes5Effect.bind (step cfg s) _) before = _
   rw [NLV_RunLaws.bind_run,NLV_RunLaws.bind_run]
   cases edge : SdkC_Source.run h (step cfg s) before with
   | mk reply log =>
     cases reply with
     | fail e => rfl
     | div => rfl
     | ok post =>
       cases post with
       | inl out => rfl
       | inr after =>
         have smaller:=decrease cfg h s after before log edge
         have room : rank after≤n := by omega
         exact ih after room log
#print axioms exact_source
#print exact_source
end AspisR1.NLV_Tree
end
