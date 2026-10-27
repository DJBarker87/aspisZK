import R1Z.PV_Inv_RawMembership
import R1Z.PV_Inv_RawInvoke
import R1Z.PV_Inv_NativeQ
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_RawNative
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawInvoke
open ProverCommitNativeQ48 (source)
local instance : DecidableEq U32 := Classical.decEq _

theorem packed_nonzero (chi : Old.Q) (hc : Canonical chi)
    (es : List (Entry Old.Q U32)) (s : Slots Old.Q U32)
    (canon : ∀ e ∈ es, Canonical e.value)
    (guard : ∀ e ∈ es, decode chi ≠ decode e.value)
    (hr : run (empty zero) es = some s) :
    ∀ slot ∈ reached s, ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot) = ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧
      field.QM31.is_zero (source operand) = ok false ∧
      kernels.inverse_q (source operand) = ok (some (source inverse)) ∧ Canonical inverse := by
  intro slot hs
  obtain ⟨i,hi,hv⟩ := PV_Inv_RawInvoke.reached_origin s slot hs
  obtain ⟨e,he,hev⟩ := PV_Inv_RawMembership.reached_origin es zero s hr i hi
  have hslot : e.value=slot := hev.trans hv
  rw [←hslot]
  exact PV_Inv_NativeQ.subtract_nonzero chi e.value hc (canon e he) (guard e he)

#print axioms packed_nonzero
end R1Z.PV_Inv_RawNative
