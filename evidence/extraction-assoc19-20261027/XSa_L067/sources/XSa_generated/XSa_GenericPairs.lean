import XRy_IndexedSum
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_GenericPairs

/-- Association preserves the complete monadic result, including fail/div. -/
theorem fold_map {A B S : Type} (xs : List A) (f : A → B)
 (step : S → B → Result S) (s : S) :
 (xs.map f).foldlM step s = xs.foldlM (fun s a => step s (f a)) s := by
 induction xs generalizing s with
 | nil => rfl
 | cons a xs ih =>
   simp only [List.map_cons,List.foldlM_cons]
   apply (bind_eq_iff _ _ _).mpr
   intro next hnext
   exact ih next

/-- Typed equal-length arrays select the same ordered list as zip. -/
theorem indexed_zip {A B : Type} (xs : List A) (ys : List B) (n : Nat)
 (hx : xs.length=n) (hy : ys.length=n) (da : A) (db : B) :
 (List.range n).map (fun i => (xs[i]?.getD da,ys[i]?.getD db)) = xs.zip ys := by
 apply List.ext_getElem
 · simp only [List.length_map,List.length_range,List.length_zip,hx,hy,Nat.min_self]
 · intro i h1 h2
   have hi : i<n := by simpa only [List.length_map,List.length_range] using h1
   have hxi : i<xs.length := by omega
   have hyi : i<ys.length := by omega
   simp only [List.getElem_map,List.getElem_range,List.getElem_zip]
   rw [List.getElem?_eq_getElem hxi,List.getElem?_eq_getElem hyi]
   rfl

#print axioms fold_map
#print axioms indexed_zip
end XSa_GenericPairs
