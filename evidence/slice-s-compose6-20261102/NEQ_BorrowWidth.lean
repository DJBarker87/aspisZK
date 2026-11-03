import NEQ_PaymentDecode
set_option autoImplicit false
noncomputable section
namespace NEQ_BorrowWidth
open Aeneas Aeneas.Std Result

def flag {T : Type} {N : Usize}
    (r : core.result.Result (Array T N) core.array.TryFromSliceError) : Bool :=
  match r with | .Ok _ => true | .Err _ => false

/-- The emitted borrowed-width guard is independent of payload type and bytes. -/
theorem status {T : Type} (N : Usize) (s : Slice T) :
    (do let r ← core.array.TryFromSharedArraySlice.try_from N s; ok (flag r)) =
      ok (decide (s.len=N)) := by
  unfold core.array.TryFromSharedArraySlice.try_from
  by_cases h : s.len=N
  · rw [dif_pos h]
    simp only [bind_tc_ok,flag,h,decide_true]
  · rw [dif_neg h]
    simp only [bind_tc_ok,flag,h,decide_false]

/-- Every reached byte-buffer payment caller keeps the SAME complete value. -/
theorem fixed216 {T : Type} (b : Array T 216#usize) :
    core.array.TryFromSharedArraySlice.try_from 216#usize b.to_slice = ok (.Ok b) := by
  have h : b.to_slice.len=216#usize := by
    simp only [Array.to_slice,Slice.len,Slice.length,b.property]
    rfl
  unfold core.array.TryFromSharedArraySlice.try_from
  rw [dif_pos h]
  rfl

#print axioms status
#print axioms fixed216
end NEQ_BorrowWidth
