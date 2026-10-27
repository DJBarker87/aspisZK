import XRs_AddLoop
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_AddAssociation
/-- All raw limbs and all addends; complete Result, including fail/div. -/
theorem add (digits : Array U32 8#usize) (n : U32) :
 XRn_Join_Release.sampler.add_small_base_p digits n =
 AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p digits n := by
 have h := XRs_AddLoop.join digits (⟨digits.to_slice,0⟩ : XRs_AddStep.Iter)
  (by exact digits.property) 8 0 rfl digits id n (XRs_AddInvariant.initial digits)
 have hc := congrArg (fun r : Result (Array U32 8#usize × U32) =>
  r >>= fun p => ok (p.2 != 0#u32,p.1)) h
 unfold XRn_Join_Release.sampler.add_small_base_p XRn_Join_intoIter
  XRn_Join_Release.sampler.add_small_base_p_loop
  AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p
  AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop
 simp only [bind_tc_ok]
 simpa only [bind_assoc_eq,XRs_AddLoop.output,bind_tc_ok] using hc
#print axioms add
end XRs_AddAssociation
