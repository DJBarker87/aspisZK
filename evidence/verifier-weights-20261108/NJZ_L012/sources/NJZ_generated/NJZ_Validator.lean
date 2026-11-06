import NJC_ValidateResult
set_option autoImplicit false
noncomputable section
namespace NJZ_Validator
open Aeneas Aeneas.Std Result
open NJC_ValidateResult
attribute [local instance] Classical.propDecidable

/-- Every entered suffix element is in range and absent from its actual prefix. -/
theorem members (pre tail : List U32) (valid : ValidFrom pre tail)
 (x : U32) (member : x∈tail) : x.val<262144 ∧ x∉pre := by
 induction tail generalizing pre with
 | nil => cases member
 | cons y ys ih =>
  rcases valid with ⟨small,absent,rest⟩
  rcases List.mem_cons.mp member with same|later
  · subst x;exact ⟨small,absent⟩
  · obtain ⟨range,notPrefix⟩ := ih (pre++[y]) rest later
    exact ⟨range,fun earlier=>notPrefix (List.mem_append_left _ earlier)⟩

theorem unique (pre tail : List U32) (valid : ValidFrom pre tail) : tail.Nodup := by
 induction tail generalizing pre with
 | nil => exact List.nodup_nil
 | cons y ys ih =>
  rcases valid with ⟨small,absent,rest⟩
  apply List.nodup_cons.mpr
  refine ⟨?_,ih (pre++[y]) rest⟩
  intro later
  have impossible := (members (pre++[y]) ys rest y later).2
  exact impossible (List.mem_append_right _ (by simp only [List.mem_singleton]))

/-- Complete source reply, including every rejected array, with domain
properties derived internally from its classification. No successful-child,
uniqueness, or caller-output premise is a root input. -/
theorem source (queries : Array U32 22#usize) :
 NJC_ValidateEmission.verifier.validate_checkpoint_queries queries=
 ok (if ValidFrom [] queries.val then core.result.Result.Ok ()
     else core.result.Result.Err NID_ResumeEmission.verifier.Error.Checkpoint) ∧
 (ValidFrom [] queries.val →
  (∀ x∈queries.val,x.val<262144) ∧ queries.val.Nodup) := by
 refine ⟨NJC_ValidateResult.source queries,?_⟩
 intro valid
 exact ⟨fun x hx=>(members [] queries.val valid x hx).1,unique [] queries.val valid⟩

#print axioms members
#print axioms unique
#print axioms source
end NJZ_Validator
