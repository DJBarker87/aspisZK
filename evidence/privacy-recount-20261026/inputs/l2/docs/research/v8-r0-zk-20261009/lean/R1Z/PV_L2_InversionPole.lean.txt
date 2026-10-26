import R1Z.PV_L2_InversionQ
import R1Z.MaskImageVR1

/-! Join the existing MODEL pole predicate to the extracted QM31 operand.
Only the explicit native slot/challenge correspondences remain hypotheses;
the nonzero conclusion is derived, rather than made a premise. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_InversionPole
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
open ProverCommitNativeQ48 (source)
open R0P R0Z.HonestValidity

theorem producer (trace : Trace QM31Exact) (lam : QM31Exact)
    (chi slot : Old.Q) (hchi : Canonical chi) (hslot : Canonical slot)
    (noPole : NoPole trace lam (decode chi)) (row : Fin 1024)
    (active : CopyActiveRow row) (index : Fin 2)
    (slot_join : decode slot = copyRowValues trace lam row CopyLink.producer index) :
    ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧
      Canonical inverse := by
  apply PV_L2_InversionQ.logup_operand chi slot hchi hslot
  rw [slot_join]
  exact (noPole row active index).1

theorem consumer (trace : Trace QM31Exact) (lam : QM31Exact)
    (chi slot : Old.Q) (hchi : Canonical chi) (hslot : Canonical slot)
    (noPole : NoPole trace lam (decode chi)) (row : Fin 1024)
    (active : CopyActiveRow row) (index : Fin 2)
    (slot_join : decode slot = copyRowValues trace lam row CopyLink.consumer index) :
    ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧
      Canonical inverse := by
  apply PV_L2_InversionQ.logup_operand chi slot hchi hslot
  rw [slot_join]
  exact (noPole row active index).2

#print axioms producer
#print axioms consumer
end R1Z.PV_L2_InversionPole
