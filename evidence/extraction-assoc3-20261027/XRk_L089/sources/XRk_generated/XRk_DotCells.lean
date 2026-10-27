import XRk_PushTrace
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRk_DotCells
/- A symbolic four-cell projection of the explicit wrapping model. This does
   not assume a no-wrap invariant or close the native P6 bridge. -/
theorem sum_cell (old next : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q)
    (j : Fin 4) (run : fast_pairing.canonical.Dot.push old a b=ok next) :
    next.sums.val[j.val]?.getD 0#u64 =
      XRk_u64 ((old.sums.val[j.val]?.getD 0#u64).val + XRk_partial ((XRk_raw a b)[j.val]?.getD 0)) := by
  unfold fast_pairing.canonical.Dot.push at run
  dsimp only at run
  split at run
  · have same := Result.ok.inj run
    subst next
    simp only [List.getElem?_map,List.getElem?_range j.isLt,Option.map_some,Option.getD_some]
  · rename_i impossible
    simp only [List.length_map,List.length_range] at impossible
    exact False.elim (impossible rfl)
#print axioms sum_cell
end XRk_DotCells
