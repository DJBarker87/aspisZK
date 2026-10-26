import R1Z.ProverRwSuccessMaskSource
import R1Z.ProverRwSuccessArithmeticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessCheckedObstruction
open Aeneas Aeneas.Std Result
-- One machine addition, no recurrence or large enumeration is reduced.
theorem checked_overflow :
    ProverRwSuccessMaskSource.field.M31.add 4294967295#u32 1#u32 =
      .fail .integerOverflow := by rfl

theorem release_succeeds :
    ∃ v, AspisR1ProducerRelease47.field.M31.add 4294967295#u32 1#u32=.ok v :=
  ProverRwSuccessArithmeticTotal.m_add _ _

theorem checked_not_release :
    ProverRwSuccessMaskSource.field.M31.add 4294967295#u32 1#u32 ≠
      AspisR1ProducerRelease47.field.M31.add 4294967295#u32 1#u32 := by
  obtain ⟨v,hv⟩ := release_succeeds
  rw [checked_overflow,hv]
  intro h
  cases h
#print axioms checked_overflow
#print axioms release_succeeds
#print axioms checked_not_release
end R1Z.ProverRwSuccessCheckedObstruction
