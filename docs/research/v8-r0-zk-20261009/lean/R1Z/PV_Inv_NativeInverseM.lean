import R1Z.PV_Inv_NativeScalar
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeInverseM
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitM31Ops48

theorem raw_nonzero (x : U32) (hn : decode x ≠ 0) : x ≠ 0#u32 := by
  intro he
  apply hn
  rw [he]
  rfl

theorem inverse_safe (x : U32) (hn : decode x ≠ 0) :
    ∃ y : U32, inverse_ref x=ok y ∧ canonical y ∧ decode y=(decode x)⁻¹ :=
  ProverCommitInterpolationInverse48.inverse_exact x (raw_nonzero x hn)

#print axioms raw_nonzero
#print axioms inverse_safe
end R1Z.PV_Inv_NativeInverseM
