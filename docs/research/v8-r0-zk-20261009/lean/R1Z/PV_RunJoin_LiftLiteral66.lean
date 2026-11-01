import R1Z.PV_RunJoin_LiftCell63
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftLiteral66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
attribute [local irreducible] PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

/-- Literal constructor callbacks preserve the raw M31 word. Normalization
happens later in the WideExact embedding, on both backend and semantic sides. -/
theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (m : U32) :
    @host_semantic.lift (types base) (selected base heap box ops) m=
      ok (PV_RunJoin_LiftCell63.lifted m) := by
  rw [PV_RunJoin_LiftCell63.complete]
  unfold selected
  rw [PV_B2_F_RawNative.preserved_61,PV_B2_F_RawNative.preserved_66]
  change (do
    let c ← ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromC
      (AspisR1ProducerRelease47.field.CM31.from_m31 m)
    ProverRwDictionaryTower.mapResult ProverRwDictionaryTower.fromQ
      (AspisR1ProducerRelease47.field.QM31.from_cm31 (ProverRwDictionaryTower.toC c)))=_
  simp only [AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.QM31.from_cm31,
    AspisR1ProducerRelease47.field.M31.ZERO,AspisR1ProducerRelease47.field.CM31.ZERO,
    ProverRwDictionaryTower.mapResult,ProverRwDictionaryTower.fromC,
    ProverRwDictionaryTower.fromQ,ProverRwDictionaryTower.toC,bind_tc_ok,
    PV_RunJoin_LiftCell63.lifted]

#print axioms complete
end R1Z.PV_RunJoin_LiftLiteral66
