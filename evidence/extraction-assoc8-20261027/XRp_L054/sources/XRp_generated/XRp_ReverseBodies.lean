import XRp_ReverseStep
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_ReverseBodies
open XRp_ReverseStep

def mk (xs : List U32) (h : xs.length ≤ Usize.max) : Iter := ⟨⟨⟨xs,h⟩,0⟩⟩
def restore (old : Iter) (x : U32) : Back := fun r =>
  ⟨if h : (r.iter.slice.val ++ [x]).length ≤ Usize.max then
      {r.iter with slice := ⟨r.iter.slice.val ++ [x],h⟩}
    else old.iter⟩

theorem zero (xs : List U32) (h : (xs ++ [0#u32]).length ≤ Usize.max)
    (hx : xs.length ≤ Usize.max) (back : Back) :
    body (mk (xs ++ [0#u32]) h) back 0#u64 =
      ok (.cont (mk xs hx,fun r => back (restore (mk (xs ++ [0#u32]) h) 0#u32 r),0#u64)) := by
  unfold body XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  simp [XRn_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    mk, restore]
  rfl

#print axioms zero
end XRp_ReverseBodies
