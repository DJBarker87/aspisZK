import FJs_WideWeights
import R1LiteralOpeningView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_ViewRows
open FJs_WideRows (K E P Alpha embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  SelectedOpeningFunctionals.functionals SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows

theorem rows (a : Alpha) (p0 p1 : P) (view : LiteralOpeningView.View)
    (ha : SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)=fun j=>embed (point a j))
    (hx0 : (view.circlePoints 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy0 : (view.circlePoints 0).val.2=embed (FJc_WeightValues.decode p0.y))
    (hx1 : (view.circlePoints 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy1 : (view.circlePoints 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1=SelectedOpeningFunctionals.rows (E := AspisWideTower.WideExact) (view.semantic.map Prod.snd) view.circlePoints := by
  have fn := FJs_WideWeights.rows a p0 p1 (view.semantic.map Prod.snd)
  dsimp only [AspisR0.ChordGeometry.Point] at fn
  exact fn view.circlePoints ha hx0 hy0 hx1 hy1

#print axioms rows
end AspisR1.FJs_ViewRows
end
