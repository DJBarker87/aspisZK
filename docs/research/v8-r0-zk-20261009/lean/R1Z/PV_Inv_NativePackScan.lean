import R1Z.PV_Inv_RawNative
import R1Z.PV_Inv_Scan
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_NativePackScan
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
open PV_Inv_RawSlots PV_Inv_RawRun PV_Inv_RawInvoke
open ProverCommitNativeQ48 (source)
local instance : DecidableEq U32 := Classical.decEq _

theorem guarded_packing (chi : Old.Q) (hc : Canonical chi)
    (es : List (Entry Old.Q U32)) (s : Slots Old.Q U32)
    (canon : ∀ e ∈ es, Canonical e.value)
    (guard : PV_Inv_Scan.scan (decode chi) true (es.map (fun e => decode e.value)) = true)
    (hr : run (empty zero) es=some s) :
    ∀ slot ∈ reached s, ∃ operand inverse : Old.Q,
      field.QM31.sub (source chi) (source slot)=ok (source operand) ∧
      Canonical operand ∧ decode operand ≠ 0 ∧ field.QM31.is_zero (source operand)=ok false ∧
      kernels.inverse_q (source operand)=ok (some (source inverse)) ∧ Canonical inverse := by
  apply PV_Inv_RawNative.packed_nonzero chi hc es s canon _ hr
  intro e he
  exact ((PV_Inv_Scan.scan_iff (decode chi) true _).mp guard).2 (decode e.value)
    (List.mem_map.mpr ⟨e,he,rfl⟩)

#print axioms guarded_packing
end R1Z.PV_Inv_NativePackScan
