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

/-- Complete factorization, without assuming constructor callback values. -/
theorem complete [ExternalTypes] (ops : ExternalFuns) (m : U32) :
    @host_semantic.lift _ ops m=(do let c ← ops.op61 m; ops.op66 c) := by
  rfl

#print axioms lifted
#print axioms word_idempotent
#print axioms normalized
#print axioms complete
end R1Z.PV_RunJoin_LiftCell63
