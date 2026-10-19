import RawCircleSampleEncodedStatePointsV1

set_option autoImplicit false
noncomputable section

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleEncodedStateBadEventLawsV1

open RawCircleSampleEncodedStatePointsV1
open RawCircleSamplePointwiseModelV1
open FS
open AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.OracleResampling
open AspisV8R19.SourceDuplexStep
open AspisR0.ChordGeometry
open R0C.SemStatement
open R0P.SemSource

attribute [local instance] Classical.propDecidable

/-- Select the successful actual first-row output and reify it as the
    corresponding R0P point. Its equality to `circleSample0` is proved below. -/
def actualRow25Point (s : State) : Point AspisWideTower.WideExact :=
  toModelPoint
    (Classical.choose (actual_row25_point_eq_model s)) .First s
    (Classical.choose (Classical.choose_spec (actual_row25_point_eq_model s)))

/-- Select the successful actual second-row output and reify it as the
    corresponding R0P point. Its equality to `circleSample1` is proved below. -/
def actualRow26Point (s : State) : Point AspisWideTower.WideExact :=
  toModelPoint
    (Classical.choose (actual_row26_point_eq_model s)) .Second s
    (Classical.choose (Classical.choose_spec (actual_row26_point_eq_model s)))

theorem actualRow25Point_eq_model (s : State) :
    actualRow25Point s = circleSample0 s := by
  exact (Classical.choose_spec
    (Classical.choose_spec (actual_row25_point_eq_model s))).2

theorem actualRow26Point_eq_model (s : State) :
    actualRow26Point s = circleSample1 s := by
  exact (Classical.choose_spec
    (Classical.choose_spec (actual_row26_point_eq_model s))).2

/-- If the actual first circle row is good, its output cannot be the second
    row's fallback. This follows because that equality itself is one of the
    row-25 bad-event disjuncts. -/
theorem actualRow25_good_excludes_fallback (s : State)
    (hgood : ¬ z0Bad' (actualRow25Point s)) :
    actualRow25Point s ≠ circleFallback1 := by
  intro heq
  apply hgood
  rw [heq]
  unfold z0Bad'
  exact Or.inr rfl

/-- The actual row-25 bad-event mass is exactly the existing one-fiber
    model bound. In particular the fallback point is already included in
    `z0Bad'`; no extra fallback atom is added. -/
theorem actual_row25_bad_mean :
    mean (fun s : State => indicator (z0Bad' (actualRow25Point s))) ≤
      (1 + deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4 := by
  classical
  have hview (s : State) :
      z0Bad' (actualRow25Point s) ↔ z0Bad' (circleSample0 s) := by
    rw [actualRow25Point_eq_model]
  rw [mean_congr (fun s => indicator_iff (hview s))]
  exact circleSample0_mass

/-- Conditional row-26 bad-event mass for the actual output representation.
    The only side condition is the preceding good row's exclusion of the
    second-row fallback, exactly as in the existing model fiber theorem. -/
theorem actual_row26_bad_mean (z0 : Point AspisWideTower.WideExact)
    (hprevious_good : ¬ z0Bad' z0) :
    mean (fun s : State => indicator (z1Bad z0 (actualRow26Point s))) ≤
      (1 + deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4 := by
  classical
  have hz0 : z0 ≠ circleFallback1 := by
    intro heq
    apply hprevious_good
    rw [heq]
    unfold z0Bad'
    exact Or.inr rfl
  have hview (s : State) :
      z1Bad z0 (actualRow26Point s) ↔ z1Bad z0 (circleSample1 s) := by
    rw [actualRow26Point_eq_model]
  rw [mean_congr (fun s => indicator_iff (hview s))]
  exact circleSample1_mass z0 hz0

#print axioms actualRow25Point_eq_model
#print axioms actualRow26Point_eq_model
#print axioms actualRow25_good_excludes_fallback
#print axioms actual_row25_bad_mean
#print axioms actual_row26_bad_mean

end RawCircleSampleEncodedStateBadEventLawsV1
end AspisR1CircleSampleWrapper
end
