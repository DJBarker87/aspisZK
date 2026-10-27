import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
namespace AspisR1.JGg_QueryTrace
open Aeneas Aeneas.Std Result

theorem read (q : Array U32 22#usize) (i : Usize) (bound : i.val<22) :
    Array.index_usize q i=ok (q.val[i.val]'(by rw [q.property];exact bound)) := by
  unfold Array.index_usize
  rw [List.getElem?_eq_getElem]
#print axioms read
end AspisR1.JGg_QueryTrace
