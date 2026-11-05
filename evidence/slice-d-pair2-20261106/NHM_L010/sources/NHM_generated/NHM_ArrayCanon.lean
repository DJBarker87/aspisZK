import NHI_CellCanon
set_option autoImplicit false
namespace NHM_ArrayCanon
open Aeneas Aeneas.Std Result

theorem read {T : Type} {n : Usize} (P : T→Prop) (a : Array T n) (i : Usize) (x : T)
 (domain : ∀ y∈a.val,P y) (run : Array.index_usize a i=ok x) : P x := by
 unfold Array.index_usize at run
 split at run
 · cases run
 · rename_i y hy
   cases Result.ok.inj run
   exact domain x (List.mem_of_getElem? hy)

/-- Canonicality is about the SAME indexed element, with its index range derived
from successful access rather than supplied as an unrelated chosen value. -/
theorem bounds {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
 (run : Array.index_usize a i=ok x) : i.val<n.val := by
 unfold Array.index_usize at run
 split at run
 · cases run
 · rename_i y hy
   have h := List.getElem?_eq_some_iff.mp hy
   have size:=a.property
   omega

#print axioms read
#print axioms bounds
end NHM_ArrayCanon
