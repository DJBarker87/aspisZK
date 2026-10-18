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

theorem external_local_packed_raw_source_success (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt))) :
    ∃ raw : Array U64 4#usize,
      state_only_poseidon.external_local_packed_raw input = .ok raw ∧
      ∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          packedNat (7 * AspisV8R15.ExactTowerBase.P) (sourceRawWord input) j := by
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
    change 8 * (7 * 2147483647) < 2^64
    norm_num
  obtain ⟨raw, htailRun, htailValues⟩ :=
    externalLocalRawTail_success bound rows hwordsBound hwide
  have hmodelWords : (fun r j => (localWord rows r j).val) = sourceRawWord input := by
    funext r j
    simpa [sourceRawWord, localWord] using (hrowsModel r j).1
  have hP : AspisR1.PoseidonExternalLocalBoundSource.P =
      AspisV8R15.ExactTowerBase.P := by
    norm_num [AspisR1.PoseidonExternalLocalBoundSource.P,
      AspisV8R15.ExactTowerBase.P]
  have hvalues : ∀ j : Fin 4,
      (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
        packedNat (7 * AspisV8R15.ExactTowerBase.P) (sourceRawWord input) j := by
    intro j
    have hv := htailValues j
    rw [hboundVal, hP] at hv
    calc
      (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          packedNat (7 * AspisV8R15.ExactTowerBase.P)
            (fun r k => (localWord rows r k).val) j := hv
      _ = packedNat (7 * AspisV8R15.ExactTowerBase.P)
            (sourceRawWord input) j := by
          exact congrArg
            (fun words : Fin 4 → Fin 4 → Nat =>
              packedNat (7 * AspisV8R15.ExactTowerBase.P) words j)
            hmodelWords
  refine ⟨raw, ?_, hvalues⟩
  unfold state_only_poseidon.external_local_packed_raw
  simp only [AspisR1.PoseidonExternalLocalInputLimbsBound.extension_limbs_map_exact,
    bind_tc_ok, hrowsRun, bind_tc_ok, hscan, bind_tc_ok, hboundRun, bind_tc_ok]
  let row0 : Array U64 4#usize := rows.val[0]'(by
    simpa [rows.property] using (show 0 < 4 by omega))
  have hrow0 : Array.index_usize rows 0#usize = .ok row0 := by
    simpa [row0] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok rows 0#usize (by decide)
  let row1 : Array U64 4#usize := rows.val[1]'(by
    simpa [rows.property] using (show 1 < 4 by omega))
  have hrow1 : Array.index_usize rows 1#usize = .ok row1 := by
    simpa [row1] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok rows 1#usize (by decide)
  let row2 : Array U64 4#usize := rows.val[2]'(by
    simpa [rows.property] using (show 2 < 4 by omega))
  have hrow2 : Array.index_usize rows 2#usize = .ok row2 := by
    simpa [row2] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok rows 2#usize (by decide)
  let row3 : Array U64 4#usize := rows.val[3]'(by
    simpa [rows.property] using (show 3 < 4 by omega))
  have hrow3 : Array.index_usize rows 3#usize = .ok row3 := by
    simpa [row3] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok rows 3#usize (by decide)
  let word00 : U64 := row0.val[0]'(by
    simpa [row0.property] using (show 0 < 4 by omega))
  have hword00 : Array.index_usize row0 0#usize = .ok word00 := by
    simpa [word00] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row0 0#usize (by decide)
  let word01 : U64 := row0.val[1]'(by
    simpa [row0.property] using (show 1 < 4 by omega))
  have hword01 : Array.index_usize row0 1#usize = .ok word01 := by
    simpa [word01] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row0 1#usize (by decide)
  let word02 : U64 := row0.val[2]'(by
    simpa [row0.property] using (show 2 < 4 by omega))
  have hword02 : Array.index_usize row0 2#usize = .ok word02 := by
    simpa [word02] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row0 2#usize (by decide)
  let word03 : U64 := row0.val[3]'(by
    simpa [row0.property] using (show 3 < 4 by omega))
  have hword03 : Array.index_usize row0 3#usize = .ok word03 := by
    simpa [word03] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row0 3#usize (by decide)
  let word10 : U64 := row1.val[0]'(by
    simpa [row1.property] using (show 0 < 4 by omega))
  have hword10 : Array.index_usize row1 0#usize = .ok word10 := by
    simpa [word10] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row1 0#usize (by decide)
  let word11 : U64 := row1.val[1]'(by
    simpa [row1.property] using (show 1 < 4 by omega))
  have hword11 : Array.index_usize row1 1#usize = .ok word11 := by
    simpa [word11] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row1 1#usize (by decide)
  let word12 : U64 := row1.val[2]'(by
    simpa [row1.property] using (show 2 < 4 by omega))
  have hword12 : Array.index_usize row1 2#usize = .ok word12 := by
    simpa [word12] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row1 2#usize (by decide)
  let word13 : U64 := row1.val[3]'(by
    simpa [row1.property] using (show 3 < 4 by omega))
  have hword13 : Array.index_usize row1 3#usize = .ok word13 := by
    simpa [word13] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row1 3#usize (by decide)
  let word20 : U64 := row2.val[0]'(by
    simpa [row2.property] using (show 0 < 4 by omega))
  have hword20 : Array.index_usize row2 0#usize = .ok word20 := by
    simpa [word20] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row2 0#usize (by decide)
  let word21 : U64 := row2.val[1]'(by
    simpa [row2.property] using (show 1 < 4 by omega))
  have hword21 : Array.index_usize row2 1#usize = .ok word21 := by
    simpa [word21] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row2 1#usize (by decide)
  let word22 : U64 := row2.val[2]'(by
    simpa [row2.property] using (show 2 < 4 by omega))
  have hword22 : Array.index_usize row2 2#usize = .ok word22 := by
    simpa [word22] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row2 2#usize (by decide)
  let word23 : U64 := row2.val[3]'(by
    simpa [row2.property] using (show 3 < 4 by omega))
  have hword23 : Array.index_usize row2 3#usize = .ok word23 := by
    simpa [word23] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row2 3#usize (by decide)
  let word30 : U64 := row3.val[0]'(by
    simpa [row3.property] using (show 0 < 4 by omega))
  have hword30 : Array.index_usize row3 0#usize = .ok word30 := by
    simpa [word30] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row3 0#usize (by decide)
  let word31 : U64 := row3.val[1]'(by
    simpa [row3.property] using (show 1 < 4 by omega))
  have hword31 : Array.index_usize row3 1#usize = .ok word31 := by
    simpa [word31] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row3 1#usize (by decide)
  let word32 : U64 := row3.val[2]'(by
    simpa [row3.property] using (show 2 < 4 by omega))
  have hword32 : Array.index_usize row3 2#usize = .ok word32 := by
    simpa [word32] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row3 2#usize (by decide)
  let word33 : U64 := row3.val[3]'(by
    simpa [row3.property] using (show 3 < 4 by omega))
  have hword33 : Array.index_usize row3 3#usize = .ok word33 := by
    simpa [word33] using
      AspisR1.RawPoseidonExternalRowReads.array_index_usize_ok row3 3#usize (by decide)
  simp only [externalLocalRawTail,
    component0ReadOps_eq, component1ReadOps_eq,
    component2ReadOps_eq, component3ReadOps_eq,
    AspisR1.PoseidonExternalPackedRawOps.component0Ops,
    AspisR1.PoseidonExternalPackedRawOps.component1Ops,
    AspisR1.PoseidonExternalPackedRawOps.component2Ops,
    AspisR1.PoseidonExternalPackedRawOps.component3Ops, bind_assoc_eq] at htailRun
  simp only [hrow0,
      hrow1,
      hrow2,
      hrow3,
      hword00,
      hword01,
      hword02,
      hword03,
      hword10,
      hword11,
      hword12,
      hword13,
      hword20,
      hword21,
      hword22,
      hword23,
      hword30,
      hword31,
      hword32,
      hword33, bind_tc_ok]
  exact htailRun

#print axioms AspisR1.PoseidonExternalPackedRawReads.component0ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component1ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component2ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.component3ReadOps_eq
#print axioms AspisR1.PoseidonExternalPackedRawReads.externalLocalRawTail_success
#print axioms external_local_packed_raw_source_success
end AspisR1.PoseidonExternalLocalPackedRawFullSource
