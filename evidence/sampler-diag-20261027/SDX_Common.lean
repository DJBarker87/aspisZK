import SDX_Join_Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace SDX_Common

theorem constant {T F : Type} (fn : core.ops.function.FnMut F Usize T)
    (c : F) (v : T) (same : ∀ i,fn.call_mut c i = ok (v,c))
    (fuel : Nat) (i : Usize) (bound : i.val + fuel ≤ Usize.max) :
    core.array.fromFnList fn fuel i c = ok (List.replicate fuel v,c) := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    rw [core.array.fromFnList,same]
    cases fuel with
    | zero => rfl
    | succ n =>
      obtain ⟨j,hj,hv⟩ := WP.spec_imp_exists
        (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
      have hbound : j.val + (n+1) ≤ Usize.max := by
        change j.val = i.val + 1 at hv
        omega
      simp only [bind_tc_ok]
      change (do
        let next ← i + 1#usize
        let (xs,c') ← core.array.fromFnList fn (n+1) next c
        ok (v::xs,c')) = _
      rw [hj,bind_tc_ok,ih j hbound]
      rfl

#print axioms constant
abbrev Iter := core.iter.adapters.rev.Rev (core.slice.iter.IterMut U32)
abbrev Back := Iter → Iter
abbrev body := SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
abbrev State := Iter × Back × U64
def step (s : State) := body s.1 s.2.1 s.2.2

def mk (xs : List U32) (h : xs.length ≤ Usize.max) : Iter := ⟨⟨⟨xs,h⟩,0⟩⟩
def restore (old : Iter) (x : U32) : Back := fun r =>
  ⟨if h : (r.iter.slice.val ++ [x]).length ≤ Usize.max then
      {r.iter with slice := ⟨r.iter.slice.val ++ [x],h⟩}
    else old.iter⟩

theorem empty (back : Back) (rem : U64) :
    body (mk [] (by simp)) back rem = ok (.done (rem,back)) := by
  simp [body, SDX_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body,
    SDX_Join_reverseNext,
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back,
    core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    mk]
#print axioms empty
end SDX_Common
