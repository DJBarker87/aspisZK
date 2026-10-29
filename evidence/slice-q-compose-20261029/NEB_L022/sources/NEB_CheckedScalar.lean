import NBQ_QChecks
import NBQ_U06
set_option autoImplicit false
namespace NEB_CheckedScalar
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- No input canonicality premise: the actual check establishes the private
callee's carrier domain on the accepted branch. -/
theorem accepted (x : NQ) (q : FIo_Native.fast_pairing.canonical.Q)
    (run : FIo_Native.fast_pairing.checked_q x=ok (.Ok q)) :
    canonQ x ∧ q=LPi_CheckedInputs.q x ∧ LPi_RawValues.Canon q := by
  by_cases hx : canonQ x
  · have same : q=LPi_CheckedInputs.q x := by
      have h := (LPi_CheckedInputs.checked x hx).symm.trans run
      cases h
      rfl
    exact ⟨hx,same,by rw [same]; exact LPi_CheckedInputs.canonical x hx⟩
  · rw [NBQ_QChecks.checked_invalid x hx] at run
    cases run

/-- The caller's accepted Result itself discharges both the count guard and
scalar canonicality. Invalid scalars and exhausted counts retain their exact
Err/state branch in the imported proofs. -/
theorem push_arguments (s out : FIo_Native.fast_pairing.EbyKDot) (v : NE) (x : NQ)
    (run : FIo_Native.fast_pairing.EbyKDot.push s v x=ok (.Ok (),out)) :
    s.count.val<4096 ∧ canonQ x ∧
      FIo_Native.fast_pairing.checked_q x=ok (.Ok (LPi_CheckedInputs.q x)) ∧
      LPi_RawValues.Canon (LPi_CheckedInputs.q x) := by
  have count : s.count.val<4096 := by
    by_contra h
    rw [NBQ_U06.limit s v x (by omega)] at run
    cases run
  have hx : canonQ x := by
    by_contra h
    rw [NBQ_QChecks.push_invalid s v x h] at run
    cases run
  exact ⟨count,hx,LPi_CheckedInputs.checked x hx,LPi_CheckedInputs.canonical x hx⟩

/-- from_wide preserves the exact lower and upper inputs; its private carrier
requirements follow from the caller's existing value domain. -/
theorem value_arguments (v : NE) (hv : canonE v) :
    FIo_Native.fast_pairing.canonical.Q.from_wide v=
      ok (Array.make 2#usize [LPi_CheckedInputs.q v.c0,LPi_CheckedInputs.q v.c1]) ∧
    LPi_RawValues.Canon (LPi_CheckedInputs.q v.c0) ∧
    LPi_RawValues.Canon (LPi_CheckedInputs.q v.c1) :=
  ⟨LPi_CheckedInputs.from_wide v,LPi_CheckedInputs.canonical v.c0 hv.1,
    LPi_CheckedInputs.canonical v.c1 hv.2⟩

#print axioms accepted
#print axioms push_arguments
#print axioms value_arguments
end NEB_CheckedScalar
