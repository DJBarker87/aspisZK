import NBL_SlicePort
set_option autoImplicit false
namespace AspisR1.NBL_ArrayPort
open Aeneas Aeneas.Std Result

/-- Generic conversion before instantiating the large View-range proof. -/
theorem source {T : Type} (slice : Slice T) (n : Usize) (size : slice.val.length=n.val) :
    core.array.TryFromSharedArraySlice.try_from n slice=ok (.Ok (⟨slice.val,size⟩ : Array T n)) := by
  unfold core.array.TryFromSharedArraySlice.try_from
  split
  · rfl
  · rename_i wrong
    exact False.elim (wrong (UScalar.eq_of_val_eq size))

#print axioms source
end AspisR1.NBL_ArrayPort
