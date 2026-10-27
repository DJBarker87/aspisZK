import JFz_Canonical
import MultiproofConeCanonicalAppend
set_option autoImplicit false
namespace AspisR1.JFz_CanonicalAppend
open Aeneas Aeneas.Std OraclePortCompactDraft MultiproofConeCanonical

theorem join (xs ys : List U8) (hx : canonical (bytesOf xs))
    (hy : canonical (bytesOf ys)) : canonical (bytesOf (xs ++ ys)) := by
  rw [bytesOf,List.map_append]
  exact (MultiproofConeCanonicalAppend.canonical_append _ _ hx.1).mpr ⟨hx,hy⟩

/-- Reassemble adjacent bounded ranges without unfolding byte data. -/
theorem slice_join {α : Type} (xs : List α) (off n m : Nat) :
    (xs.drop off).take (n+m) =
      (xs.drop off).take n ++ (xs.drop (off+n)).take m := by
  rw [← List.take_append_drop n ((xs.drop off).take (n+m))]
  simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right n m),
    List.drop_take, List.drop_drop, Nat.add_sub_cancel_left]

#print axioms join
#print axioms slice_join
end AspisR1.JFz_CanonicalAppend
