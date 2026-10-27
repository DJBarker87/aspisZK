import XRp_FromFnState
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRp_FromFnConstant

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
end XRp_FromFnConstant
