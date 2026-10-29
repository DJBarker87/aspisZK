import R1Z.PV_RunJoin_MaterialInputs49
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticScalar50
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47

def raw (q : aspis_core.field.QM31) : Old.Q :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem source (q : aspis_core.field.QM31) :
    ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source (raw q))=q := by
  cases q with | mk a b => cases a;cases b;rfl

theorem roundtrip (q : Old.Q) :
    raw (ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source q))=q := by
  cases q with | mk a b => cases a;cases b;rfl

theorem to_model (q : aspis_core.field.QM31) :
    PV_RunJoin_WeightKernel46.toQ (PV_B2_F_ConstructorCarrier.fromQ q)=
      ProverCommitNativeQ48.source (raw q) := by
  rw [←source q]
  exact PV_RunJoin_MaterialInputs49.scalar _
#print axioms raw
#print axioms source
#print axioms roundtrip
#print axioms to_model
end R1Z.PV_RunJoin_SemanticScalar50
