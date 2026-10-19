import CompPoly.Bivariate.GuruswamiSudan.Interpolation.Basic

open CompPoly
open CompPoly.GuruswamiSudan

namespace AspisWide.GSConstraintCount

abbrev Constraint (K : Type*) := CompPoly.GuruswamiSudan.InterpolationConstraint K

def pointStep {K : Type*} (acc : Array (Constraint K)) (point : K × K) : Array (Constraint K) :=
  (List.range' 0 3).foldl (fun acc a =>
    (List.range' 0 (3 - a)).foldl (fun acc b =>
      acc.push ({ x := point.1, y := point.2, xOrder := a, yOrder := b } : Constraint K)) acc) acc

def foldPoints {K : Type*} (points : Array (K × K)) : Array (Constraint K) :=
  points.toList.foldl pointStep #[]

theorem pointStep_size {K : Type*} (acc : Array (Constraint K)) (point : K × K) :
    (pointStep acc point).size = acc.size + 6 := by
  unfold pointStep
  simp [List.range'_succ]

theorem foldPoints_size {K : Type*} (points : List (K × K)) (acc : Array (Constraint K)) :
    (points.foldl pointStep acc).size = acc.size + 6 * points.length := by
  induction points generalizing acc with
  | nil => simp
  | cons point points ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, pointStep_size]
      omega

theorem interpolationConstraints_eq_foldPoints {K : Type*} (points : Array (K × K)) :
    interpolationConstraints points 3 = foldPoints points := by
  unfold interpolationConstraints foldPoints pointStep
  simp

theorem interpolationConstraints_size_three {K : Type*} (points : Array (K × K)) :
    (interpolationConstraints points 3).size = 6 * points.size := by
  rw [interpolationConstraints_eq_foldPoints]
  change (points.toList.foldl pointStep #[]).size = 6 * points.size
  rw [foldPoints_size points.toList #[]]
  simp

#print axioms interpolationConstraints_size_three

end AspisWide.GSConstraintCount
