import R1Z.ProverRwP6BindTotal
import R1Z.ProverRwSuccessPowerTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BaseTotal
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
-- Total retained release arithmetic for all raw words, without canonicality.
theorem add (a b : U32) : ∃ c, field.M31.add a b = ok c := by
  simp only [field.M31.add,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩
theorem sub (a b : U32) : ∃ c, field.M31.sub a b = ok c := by
  simp only [field.M31.sub,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩
theorem reduce (a : U64) : ∃ c, field.M31.reduce_u64 a = ok c := by
  simp only [field.M31.reduce_u64,field.reduce_u64,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩
theorem mul (a b : U32) : ∃ c, field.M31.mul a b = ok c := by
  simpa only [ProverRwSuccessPowerTotal.S.mul,
    ProverRwSuccessInverseSource.field.M31.mul] using ProverRwSuccessPowerTotal.mul_total a b

theorem double (a : U32) : ∃ c, field.M31.double a = ok c := add a a
#print axioms add
#print axioms sub
#print axioms reduce
#print axioms mul
#print axioms double
end R1Z.ProverRwP6BaseTotal
