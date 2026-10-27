import FJh_Base
import FIr_ArrayRead
set_option autoImplicit false
namespace AspisR1.FJk_CarrierRead
open Aeneas Aeneas.Std Result
/-- A successful raw descriptor read returns the SAME stored cell. -/
theorem value {T : Type} {N : Usize} (a : Array T N) (i : Usize) (out : T)
    (bound : i.val<N.val) (run : Array.index_usize a i=ok out) :
    FJh_Base.cell a ⟨i.val,bound⟩=out := by
  have slot := FIr_ArrayRead.slot a i out run
  have hi : i.val<a.val.length := by rw [a.property];exact bound
  simpa only [List.getElem?_eq_getElem hi,Option.some.injEq] using slot
#print axioms value
end AspisR1.FJk_CarrierRead
