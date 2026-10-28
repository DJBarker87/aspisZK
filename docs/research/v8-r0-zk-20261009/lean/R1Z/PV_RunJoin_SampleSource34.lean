import R1Z.PV_RunJoin_SampleTail34
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SampleSource34
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitSampleBits49
abbrev Raw := ProverCommitPrimitive47.Old.Q
variable [ExternalTypes]

theorem constructors (ops : ExternalFuns) (s : U32) :
    (do
      let c ← @aspis_core.field.CM31.from_m31 _ (ProverRwDictionaryScalar.selected ops) s
      @aspis_core.field.QM31.from_cm31 _ (ProverRwDictionaryScalar.selected ops) c) =
    .ok (PV_RunJoin_FieldData34.source (ProverCommitSamplePoint49.word s)) := by
  change (do
    let c ← ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromC
      (AspisR1ProducerRelease47.field.CM31.from_m31 s)
    ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
      (AspisR1ProducerRelease47.field.QM31.from_cm31 (ProverRwDictionaryTower.toC c))) = _
  simp only [AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.M31.ZERO,AspisR1ProducerRelease47.field.CM31.ZERO,
    ProverRwDictionaryTower.mapResult,ProverRwDictionaryTower.toC,
    ProverRwDictionaryTower.fromC,ProverRwDictionaryTower.fromQ,bind_tc_ok]
  rfl

/-- Every arithmetic and point-update prefix of the ACTUAL evaluate_assignment
is discharged. The exact remaining oracle call is at the independently defined
prefix/sample/big-endian Boolean point, preserving its entire Result. This does
not assert the still-missing semantic oracle/security-model equation. -/
theorem evaluate (ops : ExternalFuns) {F : Type} (oracleInst : host_sumcheck.Oracle F)
    (oracle : F) (p : Nat → Raw) (r assignments i : Usize)
    (hr : r.val<10) (positive : assignments.val≠0) :
    ∃ sample assignment : Usize,
      sample.val=i.val/assignments.val ∧ assignment.val=i.val%assignments.val ∧
      @host_sumcheck.evaluate_assignment _ (ProverRwDictionaryScalar.selected ops)
        F oracleInst oracle (PV_RunJoin_PointArray34.array p) r assignments i =
      oracleInst.evaluate oracle (PV_RunJoin_PointArray34.array
        (ProverCommitSamplePoint49.point p r.val assignment (UScalar.cast .U32 sample))) := by
  obtain ⟨sample,hs,hsv⟩ := UScalar.div_spec i (y := assignments) positive
  obtain ⟨assignment,ha,hav⟩ := WP.spec_imp_exists (UScalar.rem_spec i (y := assignments) positive)
  refine ⟨sample,assignment,hsv,hav,?_⟩
  let rem := Usize.wrapping_sub 9#usize r
  have hrem : rem.val=9-r.val := sub_value 9#usize r (by change r.val≤9;omega)
  unfold host_sumcheck.evaluate_assignment
  simp only [lift,bind_tc_ok,hs,ha]
  change (do
    let c ← @aspis_core.field.CM31.from_m31 _ (ProverRwDictionaryScalar.selected ops) (UScalar.cast .U32 sample)
    let q ← @aspis_core.field.QM31.from_cm31 _ (ProverRwDictionaryScalar.selected ops) c
    let point1 ← Array.update (PV_RunJoin_PointArray34.array p) r q
    let at1 ← @host_sumcheck.evaluate_assignment_loop _ (ProverRwDictionaryScalar.selected ops)
      r rem assignment point1 0#usize
    oracleInst.evaluate oracle at1) = _
  rw [← bind_assoc_eq]
  rw [constructors]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_PointArray34.update p r hr]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_SampleTail34.exact_tail ops (9-r.val) _ r rem assignment 0#usize hr hrem
    (by change 0+(9-r.val)=rem.val;omega)]
  simp only [bind_tc_ok,hrem,ProverCommitSamplePoint49.point,show (0#usize).val=0 from rfl]

#print axioms constructors
#print axioms evaluate
end R1Z.PV_RunJoin_SampleSource34
