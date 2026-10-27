import LPn_DotState
import LPn_ClaimsTotal
import LPn_ExpandTrace
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPn.Dot

/-- The raw observation is DERIVED from the actual emitted raw call on SAME
    packed input words. No raw callback/output/canonicality premise is added. -/
theorem native_result (self : FIo_Native.fast_pairing.canonical.Dot)
    (a b : FIo_Native.fast_pairing.canonical.Q) :
    ∃ out, FIo_Native.fast_pairing.canonical.Dot.push self a b=ok out ∧
      fast_pairing.canonical.Dot.push (DotState.project self) a b=ok (DotState.project out) := by
  rcases self with ⟨sums⟩
  obtain ⟨s0,s1,s2,s3,rfl⟩ := AspisR1.LPn_RawMap.shape sums
  obtain ⟨a0,a1,a2,a3,rfl⟩ := AspisR1.LPn_RawMap.shape a
  obtain ⟨b0,b1,b2,b3,rfl⟩ := AspisR1.LPn_RawMap.shape b
  obtain ⟨z,call,words⟩ := raw_same a0 a1 a2 a3 b0 b1 b2 b3
  obtain ⟨r0,r1,r2,r3,shape⟩ := AspisR1.LPn_RawMap.shape z
  rw [shape] at call words
  have observed : LPn_Kit_raw (packed a0 a1 a2 a3) (packed b0 b1 b2 b3) =
      [r0.val,r1.val,r2.val,r3.val] := words.symm
  exact DotState.source _ _ s0 s1 s2 s3 r0 r1 r2 r3 call observed

#print axioms native_result
#print axioms LPn.Expand.native_result
#print axioms LPn.Expand.length_error
#print axioms LPn.Decode.native_success
#print axioms LPn.Decode.native_error
#print axioms LPn.Decode.error_bound
#print axioms LPn.Claims.native_result
#print axioms LPn.Claims.accepted_to_cohort
#print axioms LPn.Claims.total
end LPn.Dot
