import RPu_FJs_WideRows
import R1LiteralOpeningView
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_ViewDirect
open FJs_WideRows (K E P Alpha embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  AspisR0.Opening.coeffWeight AspisR0.Opening.indicator

theorem rows (a : Alpha) (p0 p1 : P) (view : LiteralOpeningView.View)
    (ha : SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)=fun j=>embed (point a j))
    (hx0 : (view.circlePoints 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy0 : (view.circlePoints 0).val.2=embed (FJc_WeightValues.decode p0.y))
    (hx1 : (view.circlePoints 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy1 : (view.circlePoints 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1=SelectedOpeningFunctionals.rows (E := AspisWideTower.WideExact) (view.semantic.map Prod.snd) view.circlePoints := by
  funext r j
  fin_cases r
  · change FJr_InactiveRaw.raw j=AspisR0.Opening.coeffWeight rowEquiv (AspisR0.Opening.indicator R0P.copyInactiveRows) j
    rfl
  · change embed (tensorPoint (point a) j)=tensorPoint (SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)) j
    rw [ha,FJs_PointTransport.tensor]
  · change embed (tensorPoint (R0P.SemSource.successorPoint (point a)) j)=
      tensorPoint (R0P.SemSource.successorPoint (SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd))) j
    rw [ha,FJs_PointTransport.tensor,FJs_PointTransport.successor]
  · change embed (tensorPoint (R0P.SemSource.xor12Point (point a)) j)=
      tensorPoint (R0P.SemSource.xor12Point (SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd))) j
    rw [ha,FJs_PointTransport.tensor,FJs_PointTransport.xor]
  · change FJm_LibraModel.raw (embed (point a 8)) (embed (point a 9)) j=
      R0P.SemSource.libraWeight (SelectedOpeningFunctionals.alpha (view.semantic.map Prod.snd)) j
    rw [ha,←FJs_PointTransport.libra]
    unfold FJm_LibraModel.raw
    split <;> first | exact (embed.map_pow _ _).symm | skip
    split <;> simp only [map_pow,map_zero]
  · change embed (SelectedCircleWeightModel.circleWeight _ _ j.val)=
      SelectedCircleWeightModel.circleWeight (view.circlePoints 0).val.1 (view.circlePoints 0).val.2 j.val
    rw [hx0,hy0,FJs_CircleTransport.circle]
  · change embed (SelectedCircleWeightModel.circleWeight _ _ j.val)=
      SelectedCircleWeightModel.circleWeight (view.circlePoints 1).val.1 (view.circlePoints 1).val.2 j.val
    rw [hx1,hy1,FJs_CircleTransport.circle]

#print axioms rows
end AspisR1.FJs_ViewDirect
end
