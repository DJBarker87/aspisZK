import NCJ_BoxParts
import NCJ_ArrayWindows
set_option autoImplicit false
namespace NCJ_BoxWindows
open Aeneas Aeneas.Std FIn_WeightsExtract

theorem compose (a b : Weights) (variant : a.variant=b.variant)
    (factors : ∀ (k d : Fin 5) (lane : Fin 4),
      NCJ_GuardExact.pick (NCJ_GuardExact.pick (NCJ_GuardExact.pick a.factors k.val k.isLt) d.val d.isLt) lane.val lane.isLt =
      NCJ_GuardExact.pick (NCJ_GuardExact.pick (NCJ_GuardExact.pick b.factors k.val k.isLt) d.val d.isLt) lane.val lane.isLt)
    (points : ∀ (k : Fin 3) (coordinate : Fin 10),
      NCJ_GuardExact.pick (NCJ_GuardExact.pick a.points k.val k.isLt) coordinate.val coordinate.isLt =
      NCJ_GuardExact.pick (NCJ_GuardExact.pick b.points k.val k.isLt) coordinate.val coordinate.isLt)
    (extra : ∀ (i : Fin 2),NCJ_GuardExact.pick a.extra i.val i.isLt=NCJ_GuardExact.pick b.extra i.val i.isLt) : a=b := by
  apply NCJ_BoxParts.record_eq a b variant
  · exact NCJ_ArrayWindows.factor_ext a.factors b.factors factors
  · exact NCJ_ArrayWindows.points_ext a.points b.points points
  · apply NCJ_ArrayWindows.ext
    intro i hi
    exact extra ⟨i,hi⟩

#print axioms compose
end NCJ_BoxWindows
