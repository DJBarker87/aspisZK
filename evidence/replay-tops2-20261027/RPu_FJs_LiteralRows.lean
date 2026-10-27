import RPu_FJs_CircleTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_LiteralRows
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint R0P.copyInactiveRows
  AspisR0.Opening.coeffWeight AspisR0.Opening.indicator
open Aeneas Aeneas.Std
abbrev K := OraclePortCheckpointAbiC5.K
abbrev E := OraclePortCheckpointAbiC5.E
abbrev P := FJr_PairRows.P
abbrev Alpha := FJr_PairRows.Alpha
abbrev embed : K →+* E := algebraMap K E
abbrev point (a : Alpha) := FJf_ModelPoint.decoded (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ a)

theorem base (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E) :
    FJr_PairRows.rows a p0 p1 0=SelectedOpeningFunctionals.rows cs z 0 := by
  unfold FJr_PairRows.rows SelectedOpeningFunctionals.rows SemanticOpening.rows FJr_InactiveRaw.raw
  rfl

theorem original (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (ha : SelectedOpeningFunctionals.alpha cs=fun i=>embed (point a i)) :
    FJr_PairRows.rows a p0 p1 1=SelectedOpeningFunctionals.rows cs z 1 := by
  funext j
  change embed (tensorPoint (point a) j)=tensorPoint (SelectedOpeningFunctionals.alpha cs) j
  rw [ha,FJs_PointTransport.tensor]

theorem successor (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (ha : SelectedOpeningFunctionals.alpha cs=fun i=>embed (point a i)) :
    FJr_PairRows.rows a p0 p1 2=SelectedOpeningFunctionals.rows cs z 2 := by
  funext j
  change embed (tensorPoint (R0P.SemSource.successorPoint (point a)) j)=
    tensorPoint (R0P.SemSource.successorPoint (SelectedOpeningFunctionals.alpha cs)) j
  rw [ha,FJs_PointTransport.tensor,FJs_PointTransport.successor]

theorem xor (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (ha : SelectedOpeningFunctionals.alpha cs=fun i=>embed (point a i)) :
    FJr_PairRows.rows a p0 p1 3=SelectedOpeningFunctionals.rows cs z 3 := by
  funext j
  change embed (tensorPoint (R0P.SemSource.xor12Point (point a)) j)=
    tensorPoint (R0P.SemSource.xor12Point (SelectedOpeningFunctionals.alpha cs)) j
  rw [ha,FJs_PointTransport.tensor,FJs_PointTransport.xor]

theorem libra (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (ha : SelectedOpeningFunctionals.alpha cs=fun i=>embed (point a i)) :
    FJr_PairRows.rows a p0 p1 4=SelectedOpeningFunctionals.rows cs z 4 := by
  funext j
  change FJm_LibraModel.raw (embed (point a 8)) (embed (point a 9)) j=
    R0P.SemSource.libraWeight (SelectedOpeningFunctionals.alpha cs) j
  rw [ha,←FJs_PointTransport.libra]
  unfold FJm_LibraModel.raw
  split <;> first | exact (embed.map_pow _ _).symm | skip
  split <;> simp only [map_pow,map_zero]

theorem circle0 (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (hx : (z 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy : (z 0).val.2=embed (FJc_WeightValues.decode p0.y)) :
    FJr_PairRows.rows a p0 p1 5=SelectedOpeningFunctionals.rows cs z 5 := by
  funext j
  change embed (SelectedCircleWeightModel.circleWeight _ _ j.val)=
    SelectedCircleWeightModel.circleWeight (z 0).val.1 (z 0).val.2 j.val
  rw [hx,hy,FJs_CircleTransport.circle]

theorem circle1 (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (hx : (z 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy : (z 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1 6=SelectedOpeningFunctionals.rows cs z 6 := by
  funext j
  change embed (SelectedCircleWeightModel.circleWeight _ _ j.val)=
    SelectedCircleWeightModel.circleWeight (z 1).val.1 (z 1).val.2 j.val
  rw [hx,hy,FJs_CircleTransport.circle]

#print axioms base
#print axioms original
#print axioms successor
#print axioms xor
#print axioms libra
#print axioms circle0
#print axioms circle1
end AspisR1.FJs_LiteralRows
end
