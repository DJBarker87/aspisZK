import R1Z.ProverCommitM31Ops48
set_option autoImplicit false
namespace R1Z.PV_Inv_EmbedArithmetic
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47 ProverCommitM31Ops48
open ProverCommitScalar48 (embed)

theorem add_value (x y z : U32) (hv : decode z = decode x + decode y) :
    embed z = embed x + embed y := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact hv
    · simp [embed]
  · simp [embed]

theorem zero_value : embed 0#u32 = 0 := by rfl

theorem add_source (x y : U32) (hx : canonical x) (hy : canonical y) :
    ∃ z, field.M31.add x y = ok z ∧ canonical z ∧ embed z = embed x + embed y := by
  obtain ⟨z,hz,hc,hv⟩ := add_exact x y hx hy
  exact ⟨z,hz,hc,add_value x y z hv⟩

#print axioms add_value
#print axioms zero_value
#print axioms add_source
end R1Z.PV_Inv_EmbedArithmetic
