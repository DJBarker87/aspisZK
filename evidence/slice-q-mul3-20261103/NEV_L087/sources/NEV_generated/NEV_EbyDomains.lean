import NEV_EbyPushAssociation
import NEB_CheckedScalar
import LPi_PublicPush
set_option autoImplicit false
noncomputable section
namespace NEV_EbyDomains
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- SAME from_wide return gives both private operand domains. -/
theorem value (v : NE) (canonical : canonE v) :
    FIo_Native.fast_pairing.canonical.Q.from_wide v=
      ok (Array.make 2#usize [LPi_CheckedInputs.q v.c0,LPi_CheckedInputs.q v.c1]) ∧
    LPi_RawValues.Canon (LPi_CheckedInputs.q v.c0) ∧
    LPi_RawValues.Canon (LPi_CheckedInputs.q v.c1) :=
  NEB_CheckedScalar.value_arguments v canonical
/-- Accepted branch of the SAME actual checked scalar, not a premise about
successful public push or final accumulation. -/
theorem scalar (x : NQ) (q : FIo_Native.fast_pairing.canonical.Q)
    (run : NEV_EbyPushRaw.fast_pairing.checked_q x=ok (.Ok q)) :
    canonQ x ∧ q=LPi_CheckedInputs.q x ∧ LPi_RawValues.Canon q :=
  NEB_CheckedScalar.accepted x q run
/-- Successful actual push and counter are DERIVED from input-only domains. -/
theorem total (self : FIo_Native.fast_pairing.EbyKDot) (v : NE) (q : NQ)
    (hv : canonE v) (hq : canonQ q) (count : self.count.val<4096) :
    ∃ out, NEV_EbyPushRaw.fast_pairing.EbyKDot.push self v q=ok (.Ok (),out) ∧
      out.count.val=self.count.val+1 := by
  rw [NEV_EbyPushAssociation.source]
  exact LPi_PublicPush.source self v q hv hq count
#print axioms value
#print axioms scalar
#print axioms total
end NEV_EbyDomains
end
