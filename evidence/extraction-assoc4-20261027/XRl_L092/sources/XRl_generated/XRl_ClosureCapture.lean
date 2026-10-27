import XRl_ClosureAdapter
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRl_Adapter
/-- Every returned restoration callback of the actual emitted low-base-p
closure is identity. This derives a capture fact from the call, not a premise
that its internal reverse loop or division pass succeeds. -/
theorem closure_1_restoration (c : Capture) (i : Usize)
    (word : U32) (last : Capture) (restore : Capture → Capture)
    (run : emittedMut c i=ok (word,last,restore)) : restore=id := by
  unfold emittedMut sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨im,iterBack,_,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨iter,revBack,_,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨remainder,loopBack,_,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨out,_,run⟩ := bind_success _ _ _ run
  have same := congrArg (fun r => r.2.2) (Result.ok.inj run)
  exact same.symm
#print axioms closure_1_restoration
end XRl_Adapter
