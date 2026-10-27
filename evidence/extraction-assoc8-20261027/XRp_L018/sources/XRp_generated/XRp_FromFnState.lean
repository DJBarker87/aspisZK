import XRn_Join_ABI
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_FromFnState

/-- A bounded indexed traversal. The final iteration does not increment the
index, matching the actual library fromFnList's overflow/error behavior. -/
def indexed {T F : Type} (fn : core.ops.function.FnMut F Usize T) :
    Nat → Usize → F → List T → Result (List T × F)
  | 0, _, c, out => ok (out,c)
  | fuel + 1, i, c, out => do
    let (v,c') ← fn.call_mut c i
    match fuel with
    | 0 => ok (out ++ [v],c')
    | rest + 1 => do
      let next ← i + 1#usize
      indexed fn (rest + 1) next c' (out ++ [v])

theorem indexed_eq {T F : Type} (fn : core.ops.function.FnMut F Usize T)
    (fuel : Nat) (i : Usize) (c : F) (out : List T) :
    indexed fn fuel i c out = (do
      let (xs,c') ← core.array.fromFnList fn fuel i c
      ok (out ++ xs,c')) := by
  induction fuel generalizing i c out with
  | zero => simp only [indexed, core.array.fromFnList, bind_tc_ok, List.append_nil]
  | succ fuel ih =>
    cases fuel with
    | zero => simp only [indexed, core.array.fromFnList, bind_assoc_eq, bind_tc_ok]
    | succ rest =>
      simp only [indexed, core.array.fromFnList, bind_assoc_eq, bind_tc_ok]
      congr 1
      funext vc
      congr 1
      funext next
      rw [ih]
      simp only [bind_assoc_eq, bind_tc_ok, List.append_assoc, List.singleton_append]

theorem from_fn_state_eq {T F : Type} (fn : core.ops.function.FnMut F Usize T)
    (N : Usize) (c : F) :
    XRn_Join_fromFnState N fn c = (do
      let (xs,c') ← indexed fn N.val 0#usize c []
      dite (xs.length = N.val) (fun h => ok (⟨xs,h⟩,c')) (fun _ => fail .panic)) := by
  rw [indexed_eq]
  simp only [XRn_Join_fromFnState, bind_assoc_eq, bind_tc_ok, List.nil_append]

#print axioms indexed_eq
#print axioms from_fn_state_eq
end XRp_FromFnState
