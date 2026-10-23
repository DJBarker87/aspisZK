import AspisR1S9ActualWeightsNewBoxNewV3.Funs
import S9ConstructorV3Loop1CellCanonicalV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ConstructorV3PointScanBodyCanonicalV1
import S9ConstructorV3QMMulCanonicalV1
import S9ConstructorV3QMAddSubCanonicalV1
import S9PairArrayUpdateCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9ConstructorV3StatementCellCanonicalV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1

abbrev StatementRow := Array Q 10#usize
abbrev StatementPoints := Array StatementRow 3#usize

def StatementPointsCanonical (points : StatementPoints) : Prop :=
  ∀ (k : Usize) (row : StatementRow), Array.index_usize points k = .ok row →
    ∀ (i : Usize) (q : Q), Array.index_usize row i = .ok q → CanQ (toProbeQ q)

theorem update_success_bound {A : Type} {N : Usize}
    (a : Array A N) (i : Usize) (x : A) (out : Array A N)
    (h : Array.update a i x = .ok out) : i.val < N.val := by
  cases hget : a[i]? with
  | none =>
    simp only [Array.update, hget] at h
    cases h
  | some old =>
    have hsome : a.val[i.val]? = some old := by simpa using hget
    have hlen : i.val < a.val.length := (List.getElem?_eq_some_iff.mp hsome).1
    simpa only [a.property] using hlen

/-- One actual statement-cell body success derives canonicality of its four
bilinear products and the exact mutable-row write. Index arithmetic is used
only through the successful reads made by this same source execution. -/
theorem statement_cell_body_success_canonical
    (points : StatementPoints) (k : Usize) (iter iterNext : R)
    (factors factorsOut : Factors)
    (hpoints : StatementPointsCanonical points) (hfactors : FactorsCanonical factors)
    (hbody : AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop0_loop0.body
      points k iter factors = .ok (.cont (iterNext, factorsOut))) :
    FactorsCanonical factorsOut := by
  unfold AspisR1S9ActualWeightsNewBoxNewV3.weights_new_loop0_loop0.body at hbody
  obtain ⟨next, hnext, hbody⟩ := bind_success_inv
    (core.iter.range.IteratorRange.next core.iter.range.StepUsize iter) _ _ hbody
  rcases next with ⟨opt, iter1⟩
  cases opt with
  | none =>
    change ok (ControlFlow.done factors : ControlFlow (R × Factors) Factors) =
      ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    cases hbody
  | some d =>
    obtain ⟨tau, htau, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i1, hi1, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i2, hi2, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨point, hpoint, hbody⟩ := bind_success_inv (Array.index_usize points k) _ _ hbody
    obtain ⟨a, ha, hbody⟩ := bind_success_inv (Array.index_usize point i2) _ _ hbody
    obtain ⟨i3, hi3, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨i4, hi4, hbody⟩ := bind_success_inv _ _ _ hbody
    obtain ⟨b, hb, hbody⟩ := bind_success_inv (Array.index_usize point i4) _ _ hbody
    obtain ⟨u, hu, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE a) _ _ hbody
    obtain ⟨v, hv, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.sub
        AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE b) _ _ hbody
    obtain ⟨q0, hq0, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u v) _ _ hbody
    obtain ⟨q1, hq1, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a v) _ _ hbody
    obtain ⟨q2, hq2, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul u b) _ _ hbody
    obtain ⟨q3, hq3, hbody⟩ := bind_success_inv
      (AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.mul a b) _ _ hbody
    obtain ⟨mutPair, hmut, hbody⟩ := bind_success_inv (Array.index_mut_usize factors k) _ _ hbody
    rcases mutPair with ⟨old, back⟩
    change (do
      let rowOut ← Array.update old d (Array.make 4#usize [q0, q1, q2, q3] : Cell)
      ok (ControlFlow.cont (iter1, back rowOut) : ControlFlow (R × Factors) Factors)) =
        ok (ControlFlow.cont (iterNext, factorsOut) : ControlFlow (R × Factors) Factors) at hbody
    obtain ⟨rowOut, hrow, hbody⟩ := bind_success_inv _ _ _ hbody
    have hstate := ControlFlow.cont.inj (Result.ok.inj hbody)
    have hOut : back rowOut = factorsOut := congrArg Prod.snd hstate
    subst factorsOut
    have haCan := hpoints k point hpoint i2 a ha
    have hbCan := hpoints k point hpoint i4 b hb
    have hOne : CanQ (toProbeQ AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE) := by
      simpa only [toProbeQ, AspisR1S9ConstructorV3Loop1CellCanonicalV1.toProbeQ] using
        AspisR1S9ConstructorV3Loop1CellCanonicalV1.one_canonical
    have huCan : CanQ (toProbeQ u) := by
      simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
        AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical
          AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE a u hOne haCan hu
    have hvCan : CanQ (toProbeQ v) := by
      simpa only [toProbeQ, AspisR1S9ConstructorV3QMAddSubCanonicalV1.toProbeQM] using
        AspisR1S9ConstructorV3QMAddSubCanonicalV1.qm_sub_success_canonical
          AspisR1S9ActualWeightsNewBoxNewV3.field.QM31.ONE b v hOne hbCan hv
    have hq0Can := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
      u v q0 huCan hvCan hq0
    have hq1Can := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
      a v q1 haCan hvCan hq1
    have hq2Can := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
      u b q2 huCan hbCan hq2
    have hq3Can := AspisR1S9ConstructorV3QMMulCanonicalV1.generated_mul_success_canonical
      a b q3 haCan hbCan hq3
    have hCells : CellsCanonical (mapCells (Array.make 4#usize [q0, q1, q2, q3] : Cell)) := by
      change AspisR1S9ConstructorV3Loop1CellCanonicalV1.CellsCanonical
        (AspisR1S9ConstructorV3Loop1CellCanonicalV1.mapCells
          (Array.make 4#usize [q0, q1, q2, q3] : AspisR1S9ConstructorV3Loop1CellCanonicalV1.Cell))
      exact
        AspisR1S9ConstructorV3Loop1CellCanonicalV1.make4_cells_canonical
          q0 q1 q2 q3 hq0Can hq1Can hq2Can hq3Can
    have hread := index_mut_read factors k old back hmut
    have hmapped : Array.index_usize (mapFactors factors) k = .ok (mapRow old) := by
      calc
        Array.index_usize (mapFactors factors) k =
            AspisR1S9CandidateFoldMapPrimitivesV1.mapResult mapRow (Array.index_usize factors k) :=
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result mapRow factors k).symm
        _ = .ok (mapRow old) := by rw [hread]; rfl
    have hOldCan := hfactors k (mapRow old) hmapped
    have hd := update_success_bound old d (Array.make 4#usize [q0, q1, q2, q3] : Cell) rowOut hrow
    have hRowCan := AspisR1S9PairArrayUpdateCanonicalV1.update_preserves_canonical_reads
      mapCells CellsCanonical old d (Array.make 4#usize [q0, q1, q2, q3] : Cell)
      rowOut hd hrow hOldCan hCells
    exact AspisR1S9ConstructorV3PointScanBodyCanonicalV1.mutable_row_write_preserves_canonical
      factors k old rowOut back hmut hfactors hRowCan

#print axioms statement_cell_body_success_canonical
end AspisR1S9ConstructorV3StatementCellCanonicalV1
