import R1Z.PV_RunJoin_SampleDomain34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SampleCanonical34
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
abbrev Raw := Old.Q

/-- Every coordinate sent to the source oracle is canonical when its
retained challenge prefix is canonical and its sample is in the actual range. -/
theorem canonical_point (p : Nat → Raw) (r : Nat) (hr : r<10)
    (hp : ∀ k, k<r → Canonical (p k)) (a : Usize) (sample : U32) (hs : sample.val<28)
    (k : Nat) (hk : k<10) :
    Canonical (ProverCommitSamplePoint49.point p r a sample k) := by
  rw [ProverCommitSamplePoint49.point,ProverCommitSampleTail49.values_at]
  split
  · unfold ProverCommitSampleTail49.qbit
    split
    · exact ProverCommitSubtraction47.one_canonical
    · exact zero_canonical
  · rename_i outside
    by_cases he : k=r
    · subst k
      rw [Function.update_self]
      exact ProverCommitSamplePoint49.word_canonical sample hs
    · rw [Function.update_of_ne he]
      exact hp k (by omega)

variable [ExternalTypes]
/-- Exact source oracle Result on every actual worker index, with all
sample/assignment bounds and constructor domains supplied. The oracle's
own semantic law and the worker's ordered effect law remain separate P work. -/
theorem actual_worker (ops : ExternalFuns) {F : Type} (oracleInst : host_sumcheck.Oracle F)
    (oracle : F) (p : Nat → Raw) (r i : Usize) (hr : r.val<10)
    (hi : i.val<(PV_RunJoin_SampleDomain34.count r).val)
    (hp : ∀ k, k<r.val → Canonical (p k)) :
    ∃ sample assignment : Usize,
      sample.val=i.val/(PV_RunJoin_SampleDomain34.assignments r).val ∧ sample.val<28 ∧
      assignment.val=i.val%(PV_RunJoin_SampleDomain34.assignments r).val ∧ assignment.val<2^(9-r.val) ∧
      @host_sumcheck.evaluate_assignment _ (ProverRwDictionaryScalar.selected ops)
        F oracleInst oracle (PV_RunJoin_PointArray34.array p) r
          (PV_RunJoin_SampleDomain34.assignments r) i =
        oracleInst.evaluate oracle (PV_RunJoin_PointArray34.array
          (ProverCommitSamplePoint49.point p r.val assignment (UScalar.cast .U32 sample))) ∧
      ∀ k, k<10 → Canonical
        (ProverCommitSamplePoint49.point p r.val assignment (UScalar.cast .U32 sample) k) := by
  obtain ⟨ds,da⟩ := PV_RunJoin_SampleDomain34.domain r i hr hi
  obtain ⟨sample,assignment,hs,ha,he⟩ := PV_RunJoin_SampleSource34.evaluate ops oracleInst oracle p r
    (PV_RunJoin_SampleDomain34.assignments r) i hr
    (Nat.ne_of_gt (PV_RunJoin_SampleDomain34.assignments_bound r hr).1)
  have hsmall : sample.val<28 := by rw [hs]; exact ds
  have hcast : (UScalar.cast .U32 sample).val=sample.val := by scalar_tac
  refine ⟨sample,assignment,hs,hsmall,ha,?_,he,?_⟩
  · rw [ha];exact da
  · intro k hk
    exact canonical_point p r.val hr hp assignment _ (by rw [hcast];exact hsmall) k hk

#print axioms canonical_point
#print axioms actual_worker
end R1Z.PV_RunJoin_SampleCanonical34
