import R1Z.ProverCommitNativeQInverse49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativeQ
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open ProverCommitNativeQ48 (source)

theorem zero_exact (x : Old.Q) (hx : Canonical x) :
    kernels.inverse_q (source x) = ok none ↔ decode x = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨z,hz,_,_⟩ := ProverCommitNativeQInverse49.inverse x hx hn
    rw [h] at hz
    cases hz
  · intro hz
    have he := (ProverCommitNativeQInverse49.zero_iff x hx).mp hz
    rw [kernels.inverse_q,ProverCommitNativeQInverse49.zero_test]
    simp only [he,decide_true,if_true,bind_tc_ok]

theorem nonzero_test (x : Old.Q) (hx : Canonical x) (hn : decode x ≠ 0) :
    field.QM31.is_zero (source x) = ok false := by
  have h : x ≠ zero := by
    intro hz
    exact hn ((ProverCommitNativeQInverse49.zero_iff x hx).mpr hz)
  rw [ProverCommitNativeQInverse49.zero_test]
  simp only [h,decide_false]

theorem subtract_nonzero (chi slot : Old.Q) (hc : Canonical chi) (hs : Canonical slot)
    (hn : decode chi ≠ decode slot) :
    ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧ Canonical inverse := by
  obtain ⟨operand,ho,hco,hdo⟩ := ProverCommitNativeQ48.sub chi slot hc hs
  have hno : decode operand ≠ 0 := by rw [hdo]; exact sub_ne_zero.mpr hn
  obtain ⟨inverse,hi,hci,_⟩ := ProverCommitNativeQInverse49.inverse operand hco hno
  exact ⟨operand,inverse,ho,hco,hno,nonzero_test operand hco hno,hi,hci⟩

#print axioms zero_exact
#print axioms nonzero_test
#print axioms subtract_nonzero
end R1Z.PV_Inv_NativeQ
