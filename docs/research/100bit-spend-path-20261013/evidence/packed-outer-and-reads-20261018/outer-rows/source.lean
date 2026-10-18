import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import ArrayFromFnCopyStable
import PoseidonExternalLocalPackedBoundedRowsV13
import PoseidonExternalLocalInputLimbsBoundV12
import ExtractedMaskTowerAdd

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalOuterRows
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalPackedBoundedRows
open AspisR1.PoseidonExternalLocalInputLimbsBound
open AspisR1.ExtractedMaskTowerAdd (P)

abbrev QMInput := Array field.QM31 4#usize
abbrev RawInput := Array (Array U32 4#usize) 4#usize
abbrev LocalRow := Array U64 4#usize
abbrev LocalRows := Array LocalRow 4#usize

noncomputable def rowWitness (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (i : Fin 4) : LocalRow :=
  Classical.choose (local_row_from_fn_canonical_full input hcanonical i)

theorem rowWitness_spec (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (i : Fin 4) :
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input,
        outputUsize i) = .ok (rowWitness input hcanonical i) ∧
    (∀ j : Fin 4,
      ((rowWitness input hcanonical i).val[j.val]'(by
        simpa [(rowWitness input hcanonical i).property] using j.isLt)).val =
        AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula
          (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input)
          i (outputUsize j) (by simpa [outputUsize_val] using j.isLt)) ∧
    ∀ j : Fin 4,
      ((rowWitness input hcanonical i).val[j.val]'(by
        simpa [(rowWitness input hcanonical i).property] using j.isLt)).val < 7 * P :=
  Classical.choose_spec (local_row_from_fn_canonical_full input hcanonical i)

noncomputable def rowValueAt (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (n : Nat) : LocalRow :=
  if h : n < 4 then rowWitness input hcanonical ⟨n,h⟩ else Array.repeat 4#usize 0#u64

theorem outer_call_mut_success (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (i : Usize) (hi : i.val < 4) :
    state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644.call_mut
      (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input) i =
      .ok (rowValueAt input hcanonical i.val,
        AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input) := by
  let ix : Fin 4 := ⟨i.val,hi⟩
  have hrun := (rowWitness_spec input hcanonical ix).1
  have hu : outputUsize ix = i := by
    apply UScalar.eq_of_val_eq
    simpa [outputUsize_val, ix]
  have hrun' : array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input, i) =
      .ok (rowWitness input hcanonical ix) := by
    simpa only [hu] using hrun
  change (do
      let row ← array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input, i)
      ok (row, AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input)) = _
  rw [hrun']
  simp [rowValueAt, hi, rowWitness]

theorem outer_rows_success (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt))) :
    ∃ rows : LocalRows,
      array_from_fn_copy 4#usize
        (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
        state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
        (Array.repeat 4#usize 0#u64)
        (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input) = .ok rows ∧
      ∀ r : Fin 4, ∀ j : Fin 4,
        ((rows.val[r.val]'(by simpa [rows.property] using r.isLt)).val[
          j.val]'(by simpa using j.isLt)).val =
          AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula
            (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input)
            r (outputUsize j) (by simpa [outputUsize_val] using j.isLt) ∧
        ((rows.val[r.val]'(by simpa [rows.property] using r.isLt)).val[
          j.val]'(by simpa using j.isLt)).val < 7 * P := by
  let inst := state_only_poseidon.external_local_packed_raw.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU644
  let rawInput := AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input
  have hfour : (4#usize).val = 4 := by scalar_tac
  have hstable : ∀ i : Usize, i.val < (4#usize).val →
      inst.call_mut rawInput i = .ok (rowValueAt input hcanonical i.val, rawInput) := by
    intro i hi
    have hi4 : i.val < 4 := by rw [← hfour]; exact hi
    exact outer_call_mut_success input hcanonical i hi4
  let value : Nat → LocalRow := rowValueAt input hcanonical
  obtain ⟨rows, hrun, hcells⟩ :=
    AspisR1SelectedMaskProbe.array_from_fn_copy_stable
      (4#usize) (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
      inst (Array.repeat 4#usize 0#u64) rawInput value hstable
  refine ⟨rows, ?_, ?_⟩
  · simpa [inst, rawInput, value] using hrun
  · intro r j
    have hr := hcells r.val (by simpa using r.isLt)
    have houter : rows.val[r.val]'(by simpa [rows.property] using r.isLt) =
        rowWitness input hcanonical r := by
      simpa [value, rowValueAt] using hr
    have hspec := (rowWitness_spec input hcanonical r).2
    have hj := hspec.1 j
    have hb := hspec.2 j
    constructor
    · rw [houter]
      exact hj
    · rw [houter]
      exact hb

#print axioms rowWitness_spec
#print axioms outer_call_mut_success
#print axioms outer_rows_success
end AspisR1.PoseidonExternalLocalOuterRows
