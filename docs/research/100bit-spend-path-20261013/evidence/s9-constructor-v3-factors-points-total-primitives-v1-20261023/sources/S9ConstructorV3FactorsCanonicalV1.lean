import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3StatementProducerCanonicalV1
import S9ConstructorV3StatementLoopsCanonicalV1
import S9ConstructorV3PointScanLoopCanonicalV1
import S9ConstructorV3InitialFactorsCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorV3FactorsCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
open AspisR1S9ConstructorV3SuccessorCarryBodyCanonicalV1
open AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3PointScanBodyCanonicalV1
open AspisR1S9ActualWeightsNewBoxNewV3

/-- A successful actual V3 constructor produces canonical factors and stored
statement points. The producer and both factor phases are inverted from this
same call; only canonical input alpha and point coordinates remain premises.
This accepted-run property does not claim allocation totality, statement-point
semantic correctness, or closure of the source/runtime refinement boundary. -/
theorem constructor_success_factors_and_points_canonical
    (variant : Variant) (alpha : Vector) (z : Array Point 2#usize) (w : Weights)
    (halpha : VectorCanonical alpha) (hz : PointsCanonical z)
    (hnew : weights_new variant alpha z = .ok (core.result.Result.Ok w)) :
    FactorsCanonical w.factors ∧ StatementPointsCanonical w.points := by
  unfold weights_new at hnew
  obtain ⟨points, hpoints, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q8, hq8, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨q9, hq9, hnew⟩ := bind_success_inv _ _ _ hnew
  change (do
    let factors1 ← weights_new_loop0 {start := 0#usize, «end» := 3#usize} points
      AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors
    let factors2 ← weights_new_loop1 {start := 0#usize, «end» := 2#usize} z factors1
    let result ← Weights.box_from_parts variant factors2 points (Array.make 2#usize [q8,q9])
    ok (core.result.Result.Ok result)) = .ok (core.result.Result.Ok w) at hnew
  obtain ⟨factors1, hphase1, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨factors2, hphase2, hnew⟩ := bind_success_inv _ _ _ hnew
  obtain ⟨boxed, hbox, hnew⟩ := bind_success_inv _ _ _ hnew
  have hpointsCan := AspisR1S9ConstructorV3StatementProducerCanonicalV1.statement_points_success_canonical
    alpha points halpha hpoints
  have hphase1Can := AspisR1S9ConstructorV3StatementLoopsCanonicalV1.statement_outer_loop_success_canonical
    points {start := 0#usize, «end» := 3#usize}
    AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initialFactors factors1 hpointsCan
    AspisR1S9ConstructorV3InitialFactorsCanonicalV1.initial_factors_canonical hphase1
  have hphase2Can := AspisR1S9ConstructorV3PointScanLoopCanonicalV1.pointscan_loop_success_canonical
    z {start := 0#usize, «end» := 2#usize} factors1 factors2 hz hphase1Can hphase2
  have hboxed : boxed = w := core.result.Result.Ok.inj (Result.ok.inj hnew)
  subst boxed
  change Result.ok (Weights.mk variant factors2 points (Array.make 2#usize [q8,q9])) = Result.ok w at hbox
  have hw : Weights.mk variant factors2 points (Array.make 2#usize [q8,q9]) = w := Result.ok.inj hbox
  rw [← hw]
  exact ⟨hphase2Can,hpointsCan⟩

#print axioms constructor_success_factors_and_points_canonical
end AspisR1S9ConstructorV3FactorsCanonicalV1
