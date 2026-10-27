import XRs_AddLoop
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_AddAssociation
theorem pair_bind {A B C : Type} (r : Result (A × B)) (k : A → B → Result C) :
 (do let (a,b) ← r; k a b) = (r >>= fun p => k p.1 p.2) := by
 cases r with
 | ok p => cases p; rfl
 | fail e => rfl
 | div => rfl
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
 dsimp only
 simp only [pair_bind]
 simpa only [bind_assoc_eq,XRs_AddLoop.output,bind_tc_ok,XRs_AddLoop.ebody,XRs_AddLoop.ibody,XRs_AddIndexed.idx,id] using hc
#print axioms pair_bind
#print axioms add
end XRs_AddAssociation
