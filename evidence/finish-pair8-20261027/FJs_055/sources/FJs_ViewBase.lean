import FJs_ViewDirect
import R1LiteralOpeningView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_ViewBase
open FJs_WideRows (K E P Alpha embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  AspisR0.Opening.coeffWeight AspisR0.Opening.indicator

theorem value (a : Alpha) (p0 p1 : P) (view : LiteralOpeningView.View)
    (ha : SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)=fun j=>embed (point a j))
    (hx0 : (view.circlePoints 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy0 : (view.circlePoints 0).val.2=embed (FJc_WeightValues.decode p0.y))
    (hx1 : (view.circlePoints 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy1 : (view.circlePoints 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1 0=SelectedOpeningFunctionals.rows (E := AspisWideTower.WideExact) (view.semantic.map Prod.snd) view.circlePoints 0 := by
  exact congrFun (FJs_ViewDirect.rows a p0 p1 view ha hx0 hy0 hx1 hy1) 0

#print axioms value
end AspisR1.FJs_ViewBase
end
