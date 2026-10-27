import XRs_AddIndexed
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_AddInvariant
open XRs_AddStep XRs_AddIndexed
/-- Pending restorations contain only indices strictly before i. -/
structure Good (base : Iter) (back : Back) (a : Array U32 8#usize) (i : Nat) : Prop where
 restored : (back base).slice.val = a.val
 suffix : ∀ j, i ≤ j → a.val[j]? = base.slice.val[j]?
 commute : ∀ r j d, i ≤ j → back (write r j d) = write (back r) j d

theorem initial (a : Array U32 8#usize) :
 Good (⟨a.to_slice,0⟩ : Iter) id a 0 := by
 constructor
 · rfl
 · intro j h; rfl
 · intro r j d h; rfl

theorem advance (base : Iter) (back : Back) (a : Array U32 8#usize)
 (i : Nat) (digit : U32) (g : Good base back a i) :
 Good base (fun r => back (write r i digit)) (set a i digit) (i+1) := by
 constructor
 · rw [g.commute base i digit (by omega)]
   change (back base).slice.val.set i digit = a.val.set i digit
   rw [g.restored]
 · intro j h
   change (a.val.set i digit)[j]? = _
   rw [List.getElem?_set_ne (by omega),g.suffix j (by omega)]
 · intro r j d h
   rw [write_commute r j i d digit (by omega)]
   exact g.commute (write r i digit) j d (by omega)

#print axioms initial
#print axioms advance
end XRs_AddInvariant
