import Port3_NativeFinishBody
import Port3_FinishControl
import Port3_QueryStage

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_FinishStage
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
variable {W : Type}

def native (ops : FinishOps W) : Port3_NativeFinishBody.Ops W where
  op0 := ops.trace
  op1 := ops.mark
  op2 := ops.pair
  op3 := ops.newWeights
  op4 := ops.dot
  op5 := verifier.finishRelationRoundWithOps ops
  op6 := ops.folds
  ne := ops.ne

/-- Definitional parent equality; the round remains an explicit child. -/
theorem parent_eq (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
    Port3_NativeFinishBody.verifier.finish_relation (native ops) v p a obs =
      verifier.finishRelationWithOps ops v p a obs := rfl

def folds : transport.Variant → Result Usize
  | .S1 => ok 1#usize | .S2 => ok 2#usize | .D => ok 2#usize

def ne (x y : E) : Result Bool := by
  classical
  exact ok (decide (x ≠ y))

def release (ops : FinishOps W) : FinishOps W :=
  {ops with trace := fun _ _ _ => ok (), mark := Port3_QueryStage.mark,
    folds := folds, ne := ne}

theorem ne_false (x y : E) (h : ne x y=ok false) : x=y := by
  classical
  simp only [ne, Result.ok.injEq, decide_eq_false_iff_not, not_not] at h
  exact h

def finish (ops : FinishOps W) (v : VTop_Stages.verifier.View)
    (p : VTop_Stages.verifier.Prepared) (a : VTop_Stages.verifier.Accumulator)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :=
  Port3_QueryInstall.result (Port3_NativeFinishBody.verifier.finish_relation (native (release ops))
    v p a (Port3_QueryInstall.observer obs))

def installed (base : VTop_Stages.Ops) (ops : FinishOps W) : VTop_Stages.Ops :=
  {base with op19 := finish ops}

/-- The physical final message and weights consumed by this actual native
parent are the successful dot arguments; comparison is physical E equality. -/
theorem accepted_dot (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (s2 : p.variant=.S2) (h : finish ops v p a obs=ok (.Ok ())) :
    ops.dot v.final_message a.weights.deref=ok (.Ok a.rhs) ∧ a.next=22#usize := by
  have success := (Port3_QueryInstall.success_iff _ _).mp h
  rw [parent_eq] at success
  have two : (release ops).folds p.variant=ok 2#usize := by rw [s2]; rfl
  obtain ⟨alpha0,claim0,alpha1,claim1,weights,alphas,pair,actual,
    ha0,hr0,ha1,hr1,hw,hs,hpair,hpairEq,hdot,hn,hne⟩ :=
    Port3_FinishControl.finish_success (release ops) v p a
      (Port3_QueryInstall.observer obs) two success
  have eq := ne_false actual a.rhs hne
  subst actual
  exact ⟨hdot,hn⟩

#print axioms parent_eq
#print axioms ne_false
#print axioms accepted_dot
end AspisR1.Port3_FinishStage
end
