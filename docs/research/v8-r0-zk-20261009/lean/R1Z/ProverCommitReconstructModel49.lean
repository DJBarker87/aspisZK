import R1Z.ProverCommitReconstructQ49
import R1Z.ProverCommitChannelAlgebra49
/-! Exact source reconstruction is the symbolic Karatsuba reconstruction,
for every U64 input matrix. No source accumulator/component law is assumed. -/
set_option autoImplicit false
namespace R1Z.ProverCommitReconstructModel49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)

theorem model_eq (s : Nat → Nat → U64) :
    ProverCommitReconstructQ49.model s=ProverCommitChannelAlgebra49.reconstruct
      (fun c h : Fin 3 => ((s c.val h.val).val : M31Exact)) := by
  rfl

theorem exact_result (s : Nat → Nat → U64) :
    ∃ z : Old.Q, reconstruction.q (ProverCommitReconstructQ49.matrix s)=ok (ProverCommitNativeQ48.source z) ∧
      Canonical z ∧ decode z=ProverCommitChannelAlgebra49.reconstruct
        (fun c h : Fin 3 => ((s c.val h.val).val : M31Exact)) := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitReconstructQ49.exact_result s
  exact ⟨z,hz,hcz,hdz.trans (model_eq s)⟩

#print axioms model_eq
#print axioms exact_result
end R1Z.ProverCommitReconstructModel49
