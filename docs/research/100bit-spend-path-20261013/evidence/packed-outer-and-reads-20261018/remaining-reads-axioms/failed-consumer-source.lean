import Aeneas
import PoseidonExternalLocalPackedCallbackSource

import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalInputLimbsBoundV12
import PoseidonExternalLocalPackedOuterRows
import PoseidonExternalLocalBoundSource
import PoseidonExternalLocalBoundLoops
import PoseidonExternalPackedRawReads
import PoseidonExternalPackedAlgebra
import RawPoseidonExternalRowReads
import ExtractedMaskTowerAdd
import AspisV8R15.ExactTowerBase

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalPackedRawFullSource
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalPackedBoundedRows
open AspisR1.PoseidonExternalLocalInputLimbsBound
open AspisR1.PoseidonExternalLocalOuterRows
open AspisR1.PoseidonExternalLocalBoundSource
open AspisR1.PoseidonExternalLocalBoundLoops
open AspisR1.PoseidonExternalPackedRawReads
open AspisR1.PoseidonExternalPackedAlgebra
open AspisR1.RawPoseidonExternalRowReads

abbrev QMInput := Array field.QM31 4#usize
abbrev LocalRows := Array (Array U64 4#usize) 4#usize

def sourceRawWord (input : QMInput) (r j : Fin 4) : Nat :=
  AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula
    (mappedRows input) r (outputUsize j) (by simpa [outputUsize_val] using j.isLt)

@[irreducible] def sourceRawValue (input : QMInput) (j : Fin 4) : Nat :=
  packedNat (7 * AspisR1.PoseidonExternalLocalBoundSource.P) (sourceRawWord input) j

theorem external_local_packed_raw_source_success (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt))) :
    ∃ raw : Array U64 4#usize,
      state_only_poseidon.external_local_packed_raw input = .ok raw ∧
      ∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          sourceRawValue input j := by
  obtain ⟨rows, hrowsRun, hrowsModel⟩ :=
    outer_rows_success input hcanonical
  obtain ⟨bound, hboundRun, hboundVal⟩ := external_local_limb_bound_success
  have hscan := ignored_bound_scan_success rows
  have hwordsBound : ∀ r j, (localWord rows r j).val < bound.val := by
    intro r j
    have h := (hrowsModel r j).2
    rw [hboundVal]
    exact h
  have hwide : 8 * bound.val < 2^64 := by
    rw [hboundVal]
    norm_num [AspisR1.PoseidonExternalLocalBoundSource.P]
  obtain ⟨raw, htailRun, htailValues⟩ :=
    externalLocalRawTail_success bound rows hwordsBound hwide
  have hmodelWords : (fun r j => (localWord rows r j).val) = sourceRawWord input := by
    funext r j
    simpa [sourceRawWord, localWord] using (hrowsModel r j).1
  have hvalues : ∀ j : Fin 4,
      (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
        sourceRawValue input j := by
    intro j
    have hv := htailValues j
    simpa [sourceRawValue, hboundVal, hmodelWords] using hv
  refine ⟨raw, ?_, hvalues⟩
  unfold state_only_poseidon.external_local_packed_raw
  simp only [AspisR1.PoseidonExternalLocalInputLimbsBound.extension_limbs_map_exact,
    bind_tc_ok, hrowsRun, bind_tc_ok, hscan, bind_tc_ok, hboundRun, bind_tc_ok]
  simp only [externalLocalRawTail, component0ReadOps, component1ReadOps,
    component2ReadOps, component3ReadOps, readWord, bind_assoc_eq] at htailRun
  exact htailRun

#print axioms AspisR1.PoseidonExternalPackedRawReads.component0ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component1ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component2ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component3ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.externalLocalRawTail_success
#print axioms sourceRawWord
#print axioms external_local_packed_raw_source_success
end AspisR1.PoseidonExternalLocalPackedRawFullSource
