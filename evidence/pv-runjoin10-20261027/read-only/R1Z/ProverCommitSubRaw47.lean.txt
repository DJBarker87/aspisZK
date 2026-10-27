import R1Z.ProverCommitPrimitive47
/-! Isolated symbolic two-coordinate source subtraction. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSubRaw47
open Aeneas Aeneas.Std Result ProverCommitPrimitive47

theorem raw (x y : Old.Q) (lo hi : Old.C)
    (hlo : AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c0 y.c0=ok lo)
    (hhi : AspisR1Qm31ArithmeticProbe.field.CM31.sub x.c1 y.c1=ok hi) :
    AspisR1ProducerChecked47.field.QM31.sub (fromQ x) (fromQ y)=ok (fromQ ⟨lo,hi⟩) := by
  rw [subQ]
  unfold subOld
  rw [hlo]
  simp only [bind_tc_ok]
  rw [hhi]
  rfl

#print axioms raw
end R1Z.ProverCommitSubRaw47
