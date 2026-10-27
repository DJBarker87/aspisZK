import XRp_FromFnConstant
import XRp_DivisionWitness
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_SamplerRepeated
open XRp_DivisionWitness XRp_FromFnConstant
abbrev fn := XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32

theorem callback_state (i : Usize) : fn.call_mut rank i = ok (0#u32,rank) := by
  unfold fn XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32
  change (do let (v,c,restore) ← callback rank i; ok (v,restore c)) = _
  rw [emitted i]
  rfl

def zeros : Array U32 8#usize := ⟨List.replicate 8 0#u32,by simp⟩

theorem eight_digits : XRn_Join_fromFnState 8#usize fn rank = ok (zeros,rank) := by
  have h := constant fn rank 0#u32 callback_state 8 0#usize (by scalar_tac)
  unfold XRn_Join_fromFnState
  change (do
    let (xs,c) ← core.array.fromFnList fn 8 0#usize rank
    dite (xs.length = 8) (fun h => ok ((⟨xs,h⟩ : Array U32 8#usize),c)) (fun _ => fail .panic)) = _
  rw [h]
  rfl

#print axioms callback_state
#print axioms eight_digits
end XRp_SamplerRepeated
