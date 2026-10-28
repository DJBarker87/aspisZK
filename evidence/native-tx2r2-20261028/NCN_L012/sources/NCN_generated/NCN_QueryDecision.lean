import NCI_QueryInvariant
set_option autoImplicit false
namespace AspisR1.NCN_QueryDecision
open Aeneas Aeneas.Std AspisR1Stage2 CheckpointBytes4Ops

theorem accepts_iff (seen qs : List U32) :
    queryLoop seen qs = core.result.Result.Ok () ↔
      (∀ q ∈ qs, q.val < 262144) ∧ (∀ q ∈ qs, q ∉ seen) ∧ qs.Nodup := by
  constructor
  · intro h
    exact ⟨NCI_QueryInvariant.accepted_bounds seen qs h,
      NCI_QueryInvariant.accepted_fresh seen qs h,
      NCI_QueryInvariant.accepted_unique seen qs h⟩
  · intro h
    induction qs generalizing seen with
    | nil => rfl
    | cons q qs ih =>
      obtain ⟨bounds,fresh,unique⟩ := h
      obtain ⟨notMem,tailUnique⟩ := List.nodup_cons.mp unique
      have headBound := bounds q (by simp)
      have headFresh := fresh q (by simp)
      have good : ¬(q.val ≥ 262144 ∨ q ∈ seen) := by omega
      simp only [queryLoop,if_neg good]
      apply ih
      refine ⟨?_,?_,tailUnique⟩
      · intro x hx; exact bounds x (by simp [hx])
      · intro x hx hold
        rcases List.mem_append.mp hold with hold|hold
        · exact fresh x (by simp [hx]) hold
        · have eq : x=q := by simpa using hold
          subst x
          exact notMem hx

theorem append (seen pre suffix : List U32) :
    queryLoop seen (pre++suffix) =
      match queryLoop seen pre with
      | .Err e => .Err e
      | .Ok () => queryLoop (seen++pre) suffix := by
  induction pre generalizing seen with
  | nil => simp only [List.nil_append,List.append_nil,queryLoop]
  | cons q pre ih =>
    simp only [List.cons_append,queryLoop]
    split
    · rfl
    · rw [ih]
      simp only [List.append_assoc,List.singleton_append]

theorem reject_at (seen pre suffix : List U32) (q : U32)
    (prior : queryLoop seen pre = .Ok ())
    (bad : q.val ≥ 262144 ∨ q ∈ seen++pre) :
    queryLoop seen (pre++q::suffix) = .Err .Checkpoint := by
  rw [append,prior]
  exact if_pos bad

#print axioms accepts_iff
#print axioms append
#print axioms reject_at
end AspisR1.NCN_QueryDecision
