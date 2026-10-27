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
  | zero => simp [indexed, core.array.fromFnList]
  | succ fuel ih =>
    rw [indexed, core.array.fromFnList]
    cases hc : fn.call_mut c i with
    | fail e => simp [hc]
    | div => simp [hc]
    | ok vc =>
      rcases vc with ⟨v,c'⟩
      simp only [hc, bind_tc_ok]
      cases fuel with
      | zero => simp
      | succ rest =>
        cases hn : i + 1#usize with
        | fail e => simp [hn]
        | div => simp [hn]
        | ok next =>
          simp only [hn, bind_tc_ok]
              rw [ih]
          cases hs : core.array.fromFnList fn (rest + 1) next c' with
          | fail e => simp [hs]
          | div => simp [hs]
          | ok xs => rcases xs with ⟨xs,c''⟩; simp [hs, List.append_assoc]

theorem from_fn_state_eq {T F : Type} (fn : core.ops.function.FnMut F Usize T)
    (N : Usize) (c : F) :
    XRn_Join_fromFnState N fn c = (do
      let (xs,c') ← indexed fn N.val 0#usize c []
      dite (xs.length = N.val) (fun h => ok (⟨xs,h⟩,c')) (fun _ => fail .panic)) := by
  rw [indexed_eq]
  unfold XRn_Join_fromFnState
  cases h : core.array.fromFnList fn N.val 0#usize c with
  | fail e => simp [h]
  | div => simp [h]
  | ok xs => rcases xs with ⟨xs,c'⟩; simp [h]

#print axioms indexed_eq
#print axioms from_fn_state_eq
end XRp_FromFnState
