import R1Z.PV_RunJoin_BackendQInput58
import R1Z.ProverRwDictionaryEmbedding
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendMInput58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open ProverCommitPrimitive47 ProverCommitNativeOps47 PV_RunJoin_BackendMatrix58

def raw (x : U32) : Old.Q := ⟨⟨normalizeWord x,0#u32⟩,⟨0#u32,0#u32⟩⟩
def value (x : U32) : W := ProverRwDictionaryTower.fromW (embedded (normalize (raw x)))

theorem q_from (x : U32) : ProverRwDictionaryScalar.qFrom x=
    ok (ProverCommitNativeQ48.source (raw x)) := by
  simp only [ProverRwDictionaryScalar.qFrom,ProverRwDictionaryScalar.mFrom,
    AspisR1ProducerRelease47.field.P,rem_source,bind_tc_ok,
    AspisR1ProducerRelease47.field.CM31.from_m31,
    AspisR1ProducerRelease47.field.QM31.from_cm31]
  simp only [ProverCommitNativeQ48.source,raw,ProverCommitRelease47.convQ,ProverCommitRelease47.convC,
    ProverCommitPrimitive47.fromQ,ProverCommitPrimitive47.fromC,
    AspisR1ProducerRelease47.field.M31.ZERO,AspisR1ProducerRelease47.field.CM31.ZERO]

theorem candidate [ExternalTypes] (ops : ExternalFuns) :
    (ProverRwP6BodyCandidate.selected ops).op110=ProverRwDictionaryEmbedding.embed := rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected

theorem field (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base)) :
    @ExternalFuns.op110 (types base) (selected base heap box ops)=ProverRwDictionaryEmbedding.embed := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_110]
  exact @candidate (types base) ops

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (x : U32) :
    @aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
      (types base) (selected base heap box ops) x=ok (value x) := by
  change @ExternalFuns.op110 (types base) (selected base heap box ops) x=_
  rw [field]
  unfold ProverRwDictionaryEmbedding.embed
  rw [q_from]
  simp only [bind_tc_ok]
  unfold ProverCommitNativeQ48.source
  rw [(ProverCommitNativeOps47.from_qm31 (raw x)).1]
  rfl

#print axioms q_from
#print axioms candidate
#print axioms field
#print axioms complete
end R1Z.PV_RunJoin_BackendMInput58
