import R1Z.PV_RunJoin_SampleSource34
import R1Z.ProverCommitSampleModel49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointMeaning34
open Aeneas Aeneas.Std Result ProverRwFull
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
abbrev Raw := ProverCommitPrimitive47.Old.Q

def point (p : Array PV_RunJoin_FieldData34.Q 10#usize) : Fin 10 → QM31Exact :=
  fun k => PV_RunJoin_FieldData34.value (p.val[k.val]'(by rw [p.property];exact k.isLt))

theorem array_point (p : Nat → Raw) :
    point (PV_RunJoin_PointArray34.array p) = fun k => decode (p k.val) := by
  funext k
  simp only [point,PV_RunJoin_PointArray34.array,ProverCommitArray49.array,List.getElem_ofFn,
    PV_RunJoin_FieldData34.value_source]

/-- The actual caller's constructed nominal point decodes to the existing
security-model roundPoint, at the same challenge hprefix and assignment.
The challenge-hprefix equation remains explicit; no source-oracle equation
is introduced as a hidden model assumption. -/
theorem round_point (ch : R0Z.HonestView.Challenges QM31Exact) (p : Nat → Raw) (r : Fin 10)
    (hprefix : ∀ k : Fin 10, k.val<r.val → decode (p k.val)=R0Z.HonestView.alpha ch k)
    (a : Fin (2^(9-r.val))) (word : Usize) (hw : word.val=a.val) (sample : U32) :
    point (PV_RunJoin_PointArray34.array (ProverCommitSamplePoint49.point p r.val word sample)) =
      R0Z.HonestView.roundPoint ch r (sample.val : QM31Exact)
        (ProverCommitBooleanEnum49.tail (9-r.val) a) := by
  rw [array_point]
  exact ProverCommitSampleModel49.point_model ch p r hprefix a word hw sample

variable [ExternalTypes]
/-- Actual complete oracle invocation plus its decoded coordinates. The
oracle Result is retained unchanged, including inner Err and source fail/div. -/
theorem evaluated_point (ops : ExternalFuns) {F : Type} (oracleInst : host_sumcheck.Oracle F)
    (oracle : F) (ch : R0Z.HonestView.Challenges QM31Exact) (p : Nat → Raw)
    (r : Fin 10) (rw : Usize) (hrw : rw.val=r.val)
    (assignments i : Usize) (positive : assignments.val≠0)
    (hprefix : ∀ k : Fin 10, k.val<r.val → decode (p k.val)=R0Z.HonestView.alpha ch k)
    (assignment_bound : i.val%assignments.val<2^(9-r.val)) :
    ∃ (sample assignment : Usize) (a : Fin (2^(9-r.val))),
      sample.val=i.val/assignments.val ∧ assignment.val=i.val%assignments.val ∧ assignment.val=a.val ∧
      @host_sumcheck.evaluate_assignment _ (ProverRwDictionaryScalar.selected ops)
        F oracleInst oracle (PV_RunJoin_PointArray34.array p) rw assignments i =
        oracleInst.evaluate oracle (PV_RunJoin_PointArray34.array
          (ProverCommitSamplePoint49.point p r.val assignment (UScalar.cast .U32 sample))) ∧
      point (PV_RunJoin_PointArray34.array
          (ProverCommitSamplePoint49.point p r.val assignment (UScalar.cast .U32 sample))) =
        R0Z.HonestView.roundPoint ch r ((UScalar.cast .U32 sample).val : QM31Exact)
          (ProverCommitBooleanEnum49.tail (9-r.val) a) := by
  obtain ⟨sample,assignment,hs,ha,he⟩ := PV_RunJoin_SampleSource34.evaluate ops oracleInst oracle p rw
    assignments i (by rw [hrw];exact r.isLt) positive
  let a : Fin (2^(9-r.val)) := ⟨assignment.val,by rw [ha];exact assignment_bound⟩
  refine ⟨sample,assignment,a,hs,ha,rfl,?_,round_point ch p r hprefix a assignment rfl _⟩
  simpa only [hrw] using he

#print axioms point
#print axioms array_point
#print axioms round_point
#print axioms evaluated_point
end R1Z.PV_RunJoin_PointMeaning34
