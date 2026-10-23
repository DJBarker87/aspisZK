import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3Loop1CellCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3DoubleCanonicalV1
import S9PairArrayUpdateCanonicalV1
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1S9ConstructorV3PointScanBodyCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1

abbrev Point := AspisR1S9ActualWeightsNewBoxNewV3.circle.SecureCirclePoint

def PointsCanonical (z : Array Point 2#usize) : Prop :=
  ∀ (k : Usize) (point : Point), Array.index_usize z k = .ok point →
    CanQ (toProbeQ point.x) ∧ CanQ (toProbeQ point.y)

/-- The enclosing row write uses the exact successful mutable-index setter. -/
theorem mutable_row_write_preserves_canonical
    (factors : Factors) (i : Usize) (old rowOut : Row) (back : Row → Factors)
    (hmut : Array.index_mut_usize factors i = .ok (old, back))
    (hfactors : FactorsCanonical factors) (hrow : RowsCanonical (mapRow rowOut)) :
    FactorsCanonical (back rowOut) := by
  have hi := index_mut_bound factors i old back hmut
  have hback := index_mut_back_set factors i old back hi hmut
  have hlen : i.val < factors.length := by simpa only [factors.property] using hi
  obtain ⟨out, hupdate, hout⟩ := WP.spec_imp_exists (Array.update_spec factors i rowOut hlen)
  have hout' : out = back rowOut := by
    calc
      out = factors.set i rowOut := hout
      _ = back rowOut := by rw [hback]
  have hupdate' : Array.update factors i rowOut = .ok (back rowOut) := by
    simpa only [hout'] using hupdate
  exact AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    mapRow RowsCanonical factors i rowOut (back rowOut) hi hupdate' hfactors hrow

/-- Whole-body success supplies all arithmetic and update calls from that same
pointscan iteration. No independent successful child call is assumed. -/
theorem pointscan_body_success_has_execution
    (z : Array Point 2#usize) (iter iterNext : R) (factors factorsOut : Factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body
      z iter factors = .ok (.cont (iterNext, factorsOut))) :
    ∃ (k : Usize) (point : Point) (q : Q) (i : Usize) (old : Row)
      (back : Row → Factors) (rowOut : Row) (x : Q),
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some k, iterNext) ∧
      Array.index_usize z k = .ok point ∧
      AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul point.x point.y = .ok q ∧
      lift (Std.Usize.wrapping_add 3#usize k) = .ok i ∧
      Array.index_mut_usize factors i = .ok (old, back) ∧
      Array.update old 0#usize (Array.make 4#usize
        [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, point.y, point.x, q] : Cell) = .ok rowOut ∧
      AspisR1S9ActualWeightsNewBoxNewV3.double point.x = .ok x ∧
      AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
        { start := 1#usize, «end» := 5#usize } (back rowOut) k x = .ok factorsOut := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    cases hbody
  | some k =>
    obtain ⟨point, hpoint, hbody⟩ := bind_success_inv (Array.index_usize z k) _ _ hbody
    obtain ⟨q, hq, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul point.x point.y) _ _ hbody
    obtain ⟨i, hi, hbody⟩ := bind_success_inv
      (lift (Std.Usize.wrapping_add 3#usize k)) _ _ hbody
    obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv (Array.index_mut_usize factors i) _ _ hbody
    rcases mutPair with ⟨old, back⟩
    change (do
      let rowOut ← Array.update old 0#usize
        (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,
          point.y, point.x, q] : Cell)
      let x ← AspisR1S9ActualWeightsNewBoxNewV3.double point.x
      let factorsInner ← AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1_loop0
        { start := 1#usize, «end» := 5#usize } (back rowOut) k x
      ok (ControlFlow.cont (iter1, factorsInner) : ControlFlow (R × Factors) Factors)) =
        ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    obtain ⟨rowOut, hrow, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨x, hx, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨factorsInner, hinner, hbody⟩ := bind_success_inv _ _ _ hbody
    have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hiEq : iter1 = iterNext := congrArg Prod.fst hstate
    have hfEq : factorsInner = factorsOut := congrArg Prod.snd hstate
    subst iterNext
    subst factorsOut
    exact ⟨k, point, q, i, old, back, rowOut, x,
      hnext, hpoint, hq, hi, hmut, hrow, hx, hinner⟩

/-- The actual pointscan body preserves factor canonicality on its same
successful execution. Its point-coordinate premise is a successful-read
contract on the same input z, not a separately chosen point. -/
theorem pointscan_body_success_canonical
    (z : Array Point 2#usize) (iter iterNext : R) (factors factorsOut : Factors)
    (hz : PointsCanonical z) (hfactors : FactorsCanonical factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop1.body
      z iter factors = .ok (.cont (iterNext, factorsOut))) :
    FactorsCanonical factorsOut := by
  obtain ⟨k, point, q, i, old, back, rowOut, x,
      hnext, hpoint, hq, hi, hmut, hrow, hx, hinner⟩ :=
    pointscan_body_success_has_execution z iter iterNext factors factorsOut hbody
  have hp := hz k point hpoint
  have hqCan := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
    point.x point.y q hp.1 hp.2 hq
  have hxCan := AspisR1S9ConstructorV3DoubleCanonicalV1.generated_double_success_canonical
    point.x x hp.1 hx
  have hOne : CanQ (toProbeQ AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE) := by
    simpa only [toProbeQ, AspisR1S9ConstructorV3Loop1CellCanonicalV1.toProbeQ] using
      AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
  have hcells : CellsCanonical (mapCells (Array.make 4#usize
      [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE, point.y, point.x, q] : Cell)) := by
    change AspisR1S9ConstructorV3Loop1CellCanonicalV1.CellsCanonical
      (AspisR1S9ConstructorV3Loop1CellCanonicalV1.mapCells
        (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,
          point.y, point.x, q] : AspisR1S9ConstructorV3Loop1CellCanonicalV1.Cell))
    exact
      AspisR1S9ConstructorV3Loop1CellCanonicalV1.make4_cells_canonical
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE point.y point.x q hOne hp.2 hp.1 hqCan
  have hread := index_mut_read factors i old back hmut
  have hmapped : Array.index_usize (mapFactors factors) i = .ok (mapRow old) := by
    calc
      Array.index_usize (mapFactors factors) i =
          AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapRow (Array.index_usize factors i) :=
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result mapRow factors i).symm
      _ = .ok (mapRow old) := by rw [hread]; rfl
  have hOldCan := hfactors i (mapRow old) hmapped
  have hzero : (0#usize).val < (5#usize).val := by decide
  have hRowCan := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
    mapCells CellsCanonical old 0#usize
    (Array.make 4#usize [AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE,
      point.y, point.x, q] : Cell)
    rowOut hzero hrow hOldCan hcells
  have hFactorsCan := mutable_row_write_preserves_canonical
    factors i old rowOut back hmut hfactors hRowCan
  have hInvariant : invariant
      ({ start := 1#usize, «end» := 5#usize }, back rowOut, x) :=
    ⟨rfl, hFactorsCan, hxCan⟩
  exact inner_loop_success_preserves k
    { start := 1#usize, «end» := 5#usize } (back rowOut) x factorsOut hInvariant hinner

#print axioms pointscan_body_success_canonical
end AspisR1S9ConstructorV3PointScanBodyCanonicalV1
