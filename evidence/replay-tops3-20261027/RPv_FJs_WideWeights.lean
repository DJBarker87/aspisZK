import RPv_FJs_WideRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJs_WideWeights
open scoped BigOperators
open FJs_WideRows (K E P Alpha embed point)
attribute [local irreducible] QuadraticAlgebra.instInv tensorPoint

theorem rows (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E)
    (ha : SelectedOpeningFunctionals.alpha cs=fun i=>embed (point a i))
    (hx0 : (z 0).val.1=embed (FJc_WeightValues.decode p0.x))
    (hy0 : (z 0).val.2=embed (FJc_WeightValues.decode p0.y))
    (hx1 : (z 1).val.1=embed (FJc_WeightValues.decode p1.x))
    (hy1 : (z 1).val.2=embed (FJc_WeightValues.decode p1.y)) :
    FJr_PairRows.rows a p0 p1=SelectedOpeningFunctionals.rows cs z := by
  funext r
  fin_cases r
  · exact FJs_WideRows.base a p0 p1 cs z
  · exact FJs_WideRows.original a p0 p1 cs z ha
  · exact FJs_WideRows.successor a p0 p1 cs z ha
  · exact FJs_WideRows.xor a p0 p1 cs z ha
  · exact FJs_WideRows.libra a p0 p1 cs z ha
  · exact FJs_WideRows.circle0 a p0 p1 cs z hx0 hy0
  · exact FJs_WideRows.circle1 a p0 p1 cs z hx1 hy1

theorem weights (a : Alpha) (p0 p1 : P) (cs : List E)
    (z : Fin 2 → AspisR0.ChordGeometry.Point E) (k : E)
    (same : FJr_PairRows.rows a p0 p1=SelectedOpeningFunctionals.rows cs z) :
    (fun i=>∑ j : Fin 7,k^j.val*FJr_PairRows.rows a p0 p1 j i)=
      FunctionalWeights.weights (SelectedOpeningFunctionals.functionals cs z)
        (SelectedOpeningFunctionals.rawBase cs z) k := by
  rw [same]
  funext i
  exact (RawFunctionalWeights.weights_eq_raw_rows (RingHom.id E) _ k i).symm

#print axioms rows
#print axioms weights
end AspisR1.FJs_WideWeights
end
