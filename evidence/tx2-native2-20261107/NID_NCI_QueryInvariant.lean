import CheckpointBytes4Ops
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCI_QueryInvariant
open Aeneas Aeneas.Std
open AspisR1Stage2
open CheckpointBytes4Ops

theorem accepted_head (seen : List U32) (q : U32) (qs : List U32)
    (h : queryLoop seen (q::qs) = core.result.Result.Ok ()) :
    q.val < 262144 ∧ q ∉ seen ∧ queryLoop (seen ++ [q]) qs = .Ok () := by
  simp only [queryLoop] at h
  split at h
  · contradiction
  · rename_i good
    exact ⟨by omega, by tauto, h⟩

theorem accepted_bounds (seen qs : List U32)
    (h : queryLoop seen qs = core.result.Result.Ok ()) :
    ∀ q ∈ qs, q.val < 262144 := by
  induction qs generalizing seen with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨bound,_,rest⟩ := accepted_head seen q qs h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact bound
    · exact ih (seen ++ [q]) rest x hx

theorem accepted_fresh (seen qs : List U32)
    (h : queryLoop seen qs = core.result.Result.Ok ()) :
    ∀ q ∈ qs, q ∉ seen := by
  induction qs generalizing seen with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨_,fresh,rest⟩ := accepted_head seen q qs h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact fresh
    · have hf := ih (seen ++ [q]) rest x hx
      intro old
      exact hf (List.mem_append_left [q] old)

theorem accepted_unique (seen qs : List U32)
    (h : queryLoop seen qs = core.result.Result.Ok ()) : qs.Nodup := by
  induction qs generalizing seen with
  | nil => exact List.nodup_nil
  | cons q qs ih =>
    obtain ⟨_,_,rest⟩ := accepted_head seen q qs h
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (seen ++ [q]) rest⟩
    intro hq
    exact accepted_fresh (seen ++ [q]) qs rest q hq (by simp)
#print axioms accepted_head
#print axioms accepted_bounds
#print axioms accepted_fresh
#print axioms accepted_unique
end AspisR1.NCI_QueryInvariant
