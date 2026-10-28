import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverRwDictionaryScalar
import R1Z.ProverCommitArray49
import R1Z.ProverCommitSamplePoint49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointArray34
open Aeneas Aeneas.Std Result ProverRwFull ProverCommitPrimitive47
open PV_RunJoin_FieldData34

def array (p : Nat → Old.Q) : Array PV_RunJoin_FieldData34.Q 10#usize :=
  ProverCommitArray49.array 10#usize (fun i => source (p i))

theorem index (p : Nat → Old.Q) (i : Usize) (hi : i.val<10) :
    Array.index_usize (array p) i = .ok (source (p i.val)) :=
  ProverCommitArray49.index _ _ i hi

theorem update (p : Nat → Old.Q) (i : Usize) (hi : i.val<10) (z : Old.Q) :
    Array.update (array p) i (source z) = .ok (array (Function.update p i.val z)) := by
  unfold array
  rw [ProverCommitArray49.update 10#usize (fun k => source (p k)) i hi]
  congr 2
  funext k
  by_cases he : k=i.val
  · subst k; simp only [Function.update_self]
  · simp only [Function.update_of_ne he]

variable [ExternalTypes]
/-- Actual selected scalar constructors at the point-update call site. -/
theorem sample (ops : ExternalFuns) (p : Nat → Old.Q) (r : Usize) (hr : r.val<10) (s : U32) :
    (do
      let c ← @aspis_core.field.CM31.from_m31 _ (ProverRwDictionaryScalar.selected ops) s
      let q ← @aspis_core.field.QM31.from_cm31 _ (ProverRwDictionaryScalar.selected ops) c
      Array.update (array p) r q) =
    .ok (array (Function.update p r.val (ProverCommitSamplePoint49.word s))) := by
  change (do
    let c ← ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromC
      (AspisR1ProducerRelease47.field.CM31.from_m31 s)
    let q ← ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
      (AspisR1ProducerRelease47.field.QM31.from_cm31 (ProverRwDictionaryTower.toC c))
    Array.update (array p) r q) = _
  simp only [AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.M31.ZERO,AspisR1ProducerRelease47.field.CM31.ZERO,
    ProverRwDictionaryTower.mapResult,ProverRwDictionaryTower.toC,
    ProverRwDictionaryTower.fromC,ProverRwDictionaryTower.fromQ,bind_tc_ok]
  exact update p r hr (ProverCommitSamplePoint49.word s)

#print axioms array
#print axioms index
#print axioms update
#print axioms sample
end R1Z.PV_RunJoin_PointArray34
