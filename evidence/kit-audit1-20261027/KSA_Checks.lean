import XSd_InverseCompare
import XSd_FinalAudit
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRn_Join_FieldExternal
set_option autoImplicit false
namespace KSA

theorem inverse_mismatch : aspis_core.field.M31.inv 2#u32 ≠ AspisR1.SAQ_Inverse.source 2#u32 :=
  XSd_InverseCompare.mismatch

theorem qpow_two (x : aspis_core.field.QM31) : XRn_Join_qpow x 2 = ok qone := by
  have unit : aspis_core.field.QM31.mul qone qone = ok qone := by rfl
  simp [XRn_Join_qpow, unit, bind_tc_ok]

def two : aspis_core.field.QM31 := ⟨⟨2#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def four : aspis_core.field.QM31 := ⟨⟨4#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
theorem square_two : aspis_core.field.QM31.mul two two = ok four := by rfl

theorem qpow_square_false : ¬ (∀ x : aspis_core.field.QM31,
    XRn_Join_qpow x 2 = aspis_core.field.QM31.mul x x) := by
  intro h
  have e := (qpow_two two).symm.trans ((h two).trans square_two)
  have bad : qone = four := Result.ok.inj e
  have b := congrArg (fun q : aspis_core.field.QM31 => q.c0.a.val) bad
  change 1 = 4 at b
  omega

-- Small byte/canonicality probes are deliberately not universal fidelity claims.
theorem m31_zero_decode : aspis_core.field.M31.from_le_bytes
    (Array.make 4#usize [0#u8,0#u8,0#u8,0#u8]) = ok (some 0#u32) := by rfl

theorem m31_p_rejected : aspis_core.field.M31.from_le_bytes
    (Array.make 4#usize [255#u8,255#u8,255#u8,127#u8]) = ok none := by rfl

theorem carrier_roundtrip (x : aspis_core.field.QM31) : newQ (oldQ x) = x := by
  cases x with | mk a b => cases a; cases b; rfl

#print axioms inverse_mismatch
#print axioms qpow_two
#print axioms square_two
#print axioms qpow_square_false
#print axioms m31_zero_decode
#print axioms m31_p_rejected
#print axioms carrier_roundtrip
end KSA
