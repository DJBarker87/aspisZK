import LPm_PublicState
import LPf_PublicDotAllStates
import NBQ_DotBounds
set_option autoImplicit false
namespace NBQ_U06
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
/-- Native constructors begin with the same two zero accumulators and count. -/
theorem new : FIo_Native.fast_pairing.EbyKDot.new =
    ok ⟨⟨Array.repeat 4#usize 0#u64⟩,⟨Array.repeat 4#usize 0#u64⟩,0#usize⟩ := rfl
/-- Count rejection preserves the entire arbitrary prestate, even with an
invalid scalar. The first branch dominates every checked_q or push call. -/
theorem limit (s : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (cap : 4096≤s.count.val) :
    FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Err (),s) := by
  have hc : s.count ≥ FIo_Native.fast_pairing.MAX_TERMS := by
    simp only [FIo_Native.fast_pairing.MAX_TERMS]; scalar_tac
  simp only [FIo_Native.fast_pairing.EbyKDot.push,if_pos hc]
/-- The direct caller derives BOTH private operand domains from its checked
scalar and WideExact input. Complete updates are inherited from CLOSED push. -/
theorem push (s : FIo_Native.fast_pairing.EbyKDot) (value : NE) (scalar : NQ)
    (hv : canonE value) (hq : canonQ scalar) (count : s.count.val<4096) :
    ∃ (lo hi : LPm_PublicState.Raw) (out : FIo_Native.fast_pairing.EbyKDot),
      FIo_Native.fast_pairing.EbyKDot.push s value scalar=ok (.Ok (),out) ∧
      LPm_PublicState.values lo=LPi_RawValues.spec (LPi_CheckedInputs.q value.c0) (LPi_CheckedInputs.q scalar) ∧
      LPm_PublicState.values hi=LPi_RawValues.spec (LPi_CheckedInputs.q value.c1) (LPi_CheckedInputs.q scalar) ∧
      out.c0=LPm_PublicState.update s.c0 lo ∧ out.c1=LPm_PublicState.update s.c1 hi ∧
      out.count.val=s.count.val+1 := LPm_PublicState.source s value scalar hv hq count
/-- Every arbitrary native finish carrier is covered; count is unread. -/
theorem finish (s : FIo_Native.fast_pairing.EbyKDot) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish s=ok out ∧ canonE out := by
  obtain ⟨out,run,a,b,c,d,e,f,g,h⟩ := LPf_PublicDotAllStates.source s
  refine ⟨out,run,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩,⟨⟨?_,?_⟩,⟨?_,?_⟩⟩⟩
  all_goals omega
#print axioms new
#print axioms limit
#print axioms push
#print axioms finish
end NBQ_U06
