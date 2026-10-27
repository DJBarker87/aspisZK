import FJs_FunctionalWeights
import R1LiteralOpeningView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_ViewRows
open FJs_LiteralRows (K E P Alpha embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows

theorem rows (a : Alpha) (p0 p1 : P) (view : LiteralOpeningView.View)
    (ha : SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)=fun j=>embed (point a j))
    (hx0 : (view.circlePoints 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy0 : (view.circlePoints 0).val.2=embed (FJc_WeightValues.decode p0.y))
    (hx1 : (view.circlePoints 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy1 : (view.circlePoints 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1=SelectedOpeningFunctionals.rows (E := E) (view.semantic.map Prod.snd) view.circlePoints := by
  let z : Fin 2 → AspisR0.ChordGeometry.Point E := fun j=>⟨(view.circlePoints j).val,(view.circlePoints j).property⟩
  have h := FJs_FunctionalWeights.rows a p0 p1 (view.semantic.map Prod.snd) z ha hx0 hy0 hx1 hy1
  exact h

#print axioms rows
end AspisR1.FJs_ViewRows
end
