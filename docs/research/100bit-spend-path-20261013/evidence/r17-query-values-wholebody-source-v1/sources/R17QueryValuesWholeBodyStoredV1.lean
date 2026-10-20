import R17QueryValuesWholeBodyV21

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17QueryValuesWholeBodyStoredV1

open R17QueryValuesWholeBodyV21
open R17QueryValuesEntryActualV1
open AspisR1QueryGeometryActual AspisCircleGroupOrder
open R17QueryPerItemValuesV2 R17FibrePointLineNodeActual

/-- The explicit parameter record is populated by the accepted concrete
current-domain and current-M31 operation records used by the stored theorem. -/
def actualSourceCallees : SourceCallees where
  fibrePoint := fun i => fast_domain.fibre_point actualCMOps i
  lineNode := fun i => R17FibrePointLineNodeActual.line_node actualCMOps actualM31Ops i
  mul := actualM31Ops.mul
  double := actualM31Ops.double
  sub := actualM31Ops.sub
  one := 1#u32

theorem direct_eq_queryValuesEntry
    (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31)) :
    directWithCallees actualSourceCallees q anyCheck =
      R17QueryValuesEntryActualV1.queryValuesEntry q anyCheck := by
  unfold directWithCallees R17QueryValuesEntryActualV1.queryValuesEntry
    actualSourceCallees
  simp only [queryErrorBranch_matches_emitted_closure,
    HDiv.hDiv, HMul.hMul, HAdd.hAdd]
  congr 1

theorem emittedRaw_success_stored
    (q : Std.U32)
    (anyCheck : core.slice.iter.Iter field.M31 →
      Result (Bool × core.slice.iter.Iter field.M31))
    (arr : Array field.M31 5#usize) (line_z : field.M31)
    (h : emittedRawWithCallees actualSourceCallees anyCheck q =
      .ok (.Ok (arr, line_z))) :
    ∃ (u ix iy : domain.FibreIndex)
      (hu : u.val < 262144) (hix : ix.val < 262144)
      (hiy : iy.val < 262144)
      (point : domain.Point field.M31) (line_x line_y : field.M31),
      ix.val = (u.val / 4) * 4 ∧ iy.val = (u.val / 4) * 4 + 3 ∧
      (⟨(R17FibrePointDecodedProduct.decodePoint point).1,
         (R17FibrePointDecodedProduct.decodePoint point).2⟩ : R17TableBasePowerBridge.ZC) =
        R17TableCirclePowerBridge.circleCoords
          (AspisV7ExactOneFoldDomains.storedInitialFibrePoint20
            (⟨u.val, hu⟩ : Fin 262144)) ∧
      decoded line_x = AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨ix.val, hix⟩ : Fin 262144) ∧
      decoded line_y = AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨iy.val, hiy⟩ : Fin 262144) ∧
      decoded line_z = 2 * (AspisV7ExactOneFoldDomains.storedFirstLineX18
          (⟨ix.val, hix⟩ : Fin 262144)) ^ 2 - 1 ∧
      ∃ it it', anyCheck it = .ok (false, it') := by
  have hEq := emittedRawWithCallees_eq_directWithCallees actualSourceCallees q anyCheck
  have hDirect : directWithCallees actualSourceCallees q anyCheck = .ok (.Ok (arr, line_z)) := by
    exact hEq.symm ▸ h
  have hEntry : R17QueryValuesEntryActualV1.queryValuesEntry q anyCheck =
      .ok (.Ok (arr, line_z)) := by
    rw [← direct_eq_queryValuesEntry q anyCheck]
    exact hDirect
  exact R17QueryValuesEntryActualV1.successful_queryValuesEntry_stored
    q anyCheck arr line_z hEntry

#print axioms direct_eq_queryValuesEntry
#print axioms emittedRaw_success_stored

end R17QueryValuesWholeBodyStoredV1
