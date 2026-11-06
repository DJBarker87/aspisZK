import NJC_ValidateCalls
set_option autoImplicit false
noncomputable section
namespace NJC_ValidateResult
open Aeneas Aeneas.Std Result AspisR1 NIL_Carriers

def ValidFrom : List U32 → List U32 → Prop
 | _,[] => True
 | pre,x::tail => x.val<262144 ∧ x∉pre ∧ ValidFrom (pre++[x]) tail

/-- Full range/duplicate classification for every suffix and arbitrary prefix.
It is not an acceptance precondition. -/
theorem model (pre tail : List U32) :
 CheckpointBytes4Ops.queryLoop pre tail=
 if ValidFrom pre tail then .Ok () else .Err .Checkpoint := by
 classical
 induction tail generalizing pre with
 | nil => simp only [CheckpointBytes4Ops.queryLoop,ValidFrom,if_true]
 | cons x tail ih =>
  unfold CheckpointBytes4Ops.queryLoop
  by_cases bad : x.val≥262144 ∨ x∈pre
  · have invalid : ¬ValidFrom pre (x::tail) := by
     intro ⟨small,absent,_⟩
     rcases bad with large|present
     · omega
     · exact absent present
    rw [if_pos bad,if_neg invalid]
  · have small : x.val<262144 := by omega
    have absent : x∉pre := fun present=>bad (Or.inr present)
    simp only [if_neg bad,ValidFrom,small,absent,true_and]
    exact ih _

/-- Exact fresh frozen-validator reply at the SAME array22, both arms, with no
successful-result premise and no strengthened caller domain. -/
theorem source (queries : Array U32 22#usize) :
 NJC_ValidateEmission.verifier.validate_checkpoint_queries queries=
 ok (if ValidFrom [] queries.val then core.result.Result.Ok ()
     else core.result.Result.Err NID_ResumeEmission.verifier.Error.Checkpoint) := by
 classical
 unfold NJC_ValidateEmission.verifier.validate_checkpoint_queries
 rw [NJC_ValidatePort.loop_exact queries [] queries.val 0#usize rfl rfl,model]
 by_cases good : ValidFrom [] queries.val
 · rw [if_pos good];rfl
 · rw [if_neg good];rfl

#print axioms model
#print axioms source
end NJC_ValidateResult
