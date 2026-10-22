import S4FromFnP6GeneratedTrace

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HighTermsStepLemmaV1

/-- One generated P6 FnMut step follows from the actual callback result and
successful checked cursor increment. -/
theorem fnMutStep_of_successful_call {T F : Type}
    (cb : core.ops.function.FnMut F Usize T)
    (closure : F) (cursor : Usize) (index : Nat) (value : T)
    (closureNext : F) (cursorNext : Usize)
    (hcall : cb.call_mut closure cursor = .ok (value, closureNext))
    (hadd : (cursor + 1#usize : Result Usize) = .ok cursorNext) :
    AspisR1FromFnP6Generated.fnMutStep cb (closure, cursor) index =
      .ok (value, (closureNext, cursorNext)) := by
  change (do
    let (value, state') ← cb.call_mut closure cursor
    let index' ← cursor + 1#usize
    .ok (value, (state', index'))) = .ok (value, (closureNext, cursorNext))
  rw [hcall, hadd]
  rfl

#print axioms fnMutStep_of_successful_call

end AspisR1S9HighTermsStepLemmaV1
