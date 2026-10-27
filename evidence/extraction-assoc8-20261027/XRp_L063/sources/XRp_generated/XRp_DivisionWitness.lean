import XRp_RestoreChain
import XRo_Join_DivPass
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_DivisionWitness
open XRp_ReverseStep XRp_ReverseBodies XRp_ReversePass XRp_RestoreChain

def rank : Array U32 8#usize := ⟨limbs 7,by simp [limbs]⟩
abbrev callback := XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut

theorem emitted (i : Usize) : callback rank i = ok (0#u32,rank,id) := by
  unfold callback XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  change (do
    let (rem,back) ← loop step (state 7 (by decide),id,0#u64)
    let digit ← lift (UScalar.cast .U32 rem)
    ok (digit,Array.from_slice rank (back (state 7 (by decide))).iter.slice,id)) = _
  rw [loop_pass]
  change ok (0#u32,Array.from_slice rank
    ((finish 7 (by decide) id) (state 7 (by decide))).iter.slice,id) = _
  have hcap : ((state 7 (by decide)).iter.slice.val ++ limbs 7).length ≤ Usize.max := by
    change 16 ≤ Usize.max
    scalar_tac
  rw [finish_append 7 (by decide) id (state 7 (by decide)) hcap]
  simp [appendIter,Array.from_slice,state,mk,rank,limbs]
  rfl

#print axioms emitted
end XRp_DivisionWitness
