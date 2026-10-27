import XRk_ABI
open Aeneas Aeneas.Std Result
namespace XRk_AdapterLaws
def forget {A B : Type} : Result (A × B) → Result A
  | .ok (a,_) => .ok a
  | .fail e => .fail e
  | .div => .div
/- The state-retaining from_fn adapter projects to the unchanged external,
   including failure and divergence. No claim about native closure P6. -/
theorem from_fn_projection {T F : Type} (N : Usize)
    (fn : core.ops.function.FnMut F Usize T) (c : F) :
    forget (XRk_fromFnState N fn c) = core.array.from_fn N fn c := by
  unfold XRk_fromFnState core.array.from_fn
  cases h : core.array.fromFnList fn N.val 0#usize c with
  | fail e => simp only [h,bind_tc_fail,forget]
  | div => simp only [h,bind_tc_div,forget]
  | ok r =>
    rcases r with ⟨values,last⟩
    simp only [h,bind_tc_ok]
    dsimp only
    split_ifs <;> rfl
#print axioms from_fn_projection
end XRk_AdapterLaws
