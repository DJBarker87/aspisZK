import Port3_FinishStage

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_FinishAny
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

/-- Physical final dot comparison is independent of variant/fold count.
The only success premise is the same emitted parent call. -/
theorem comparison (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))
    (h : verifier.finishRelationWithOps ops v p a obs=ok (.Ok ())) :
    ∃ actual, ops.dot v.final_message a.weights.deref=ok (.Ok actual) ∧
      a.next=22#usize ∧ ops.ne actual a.rhs=ok false := by
  unfold verifier.finishRelationWithOps at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals
    refine ⟨_,by assumption,?_,by assumption⟩
    aesop (add simp [bne_iff_ne])

theorem accepted_dot (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (h : Port3_FinishStage.finish ops v p a obs=ok (.Ok ())) :
    ops.dot v.final_message a.weights.deref=ok (.Ok a.rhs) ∧ a.next=22#usize := by
  have success := (Port3_QueryInstall.success_iff _ _).mp h
  rw [Port3_FinishStage.parent_eq] at success
  obtain ⟨actual,dot,hn,eq⟩ := comparison (Port3_FinishStage.release ops) v p a
    (Port3_QueryInstall.observer obs) success
  have same := Port3_FinishStage.ne_false actual a.rhs eq
  subst actual
  exact ⟨dot,hn⟩

#print axioms comparison
#print axioms accepted_dot
end AspisR1.Port3_FinishAny
end
