import R1Z.PV_RunJoin_BackendMInput58
import R1Z.PV_RunJoin_SemanticScalar50
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftCell63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open ProverCommitPrimitive47 ProverCommitNativeOps47
abbrev Q := aspis_core.field.QM31

def lifted (m : U32) : Q := ⟨⟨m,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem word_idempotent (m : U32) : normalizeWord (normalizeWord m)=normalizeWord m := by
  apply UScalar.eq_of_val_eq
  rw [normalize_val,normalize_val,Nat.mod_mod]

theorem normalized (m : U32) :
    normalize (PV_RunJoin_SemanticScalar50.raw (lifted m))=
      normalize (PV_RunJoin_BackendMInput58.raw m) := by
  simp only [ProverCommitNativeOps47.normalize,PV_RunJoin_SemanticScalar50.raw,lifted,PV_RunJoin_BackendMInput58.raw,
    word_idempotent]

theorem candidate61 [ExternalTypes] (ops : ExternalFuns) (m : U32) :
    (ProverRwP6BodyCandidate.selected ops).op61 m=ok (⟨m,0#u32⟩ : aspis_core.field.CM31) := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

theorem candidate66 [ExternalTypes] (ops : ExternalFuns) (c : aspis_core.field.CM31) :
    (ProverRwP6BodyCandidate.selected ops).op66 c=ok (⟨c,⟨0#u32,0#u32⟩⟩ : Q) := by
  unfold ProverRwP6BodyCandidate.selected ProverRwP6BoundaryInstall.selected
  rfl

attribute [local irreducible] PV_B2_F_ResourceFamilies.selected PV_B2_E_GammaOriginal.selected
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected

theorem field61 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (m : U32) :
    @ExternalFuns.op61 (types base) (selected base heap box ops) m=ok (⟨m,0#u32⟩ : aspis_core.field.CM31) := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_61]
  exact @candidate61 (types base) ops m

theorem field66 (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (c : aspis_core.field.CM31) :
    @ExternalFuns.op66 (types base) (selected base heap box ops) c=ok (⟨c,⟨0#u32,0#u32⟩⟩ : Q) := by
  unfold selected
  rw [PV_B2_F_RawNative.preserved_66]
  exact @candidate66 (types base) ops c

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (m : U32) :
    @host_semantic.lift (types base) (selected base heap box ops) m=ok (lifted m) := by
  simp only [host_semantic.lift,aspis_core.field.CM31.from_m31,aspis_core.field.QM31.from_cm31,
    field61,field66,bind_tc_ok,lifted]

#print axioms lifted
#print axioms word_idempotent
#print axioms normalized
#print axioms candidate61
#print axioms candidate66
#print axioms field61
#print axioms field66
#print axioms complete
end R1Z.PV_RunJoin_LiftCell63
