import R1Z.ProverCommitScalar48
import R1Z.ProverCommitM31Ops48
/-! The source scalar embedding is the fixed tower's ring homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitInterpolationEmbed48
open Aeneas.Std
open AspisV8R15.ExactTowerBase (M31Exact QM31Exact)

def embed : M31Exact →+* QM31Exact := algebraMap M31Exact QM31Exact

theorem source_embed (x : U32) : ProverCommitScalar48.embed x=embed (ProverCommitM31Ops48.decode x) := by
  rfl

#print axioms source_embed
end R1Z.ProverCommitInterpolationEmbed48
