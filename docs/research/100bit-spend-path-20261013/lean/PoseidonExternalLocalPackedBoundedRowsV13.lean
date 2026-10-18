import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalPackedCallbackSource
import PoseidonExternalPackedAlgebra
import RawPoseidonExternalRowReads
import RawPoseidonExternalRows
import ExtractedMaskTowerAdd
import PoseidonExternalLocalInputLimbsBoundV12

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalPackedBoundedRows
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalPackedCallbackSource
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonExternalRows
open AspisR1.ExtractedMaskTowerAdd (P)

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

def outputUsize (output : Fin 4) : Usize :=
  Usize.ofNatCore output.val (small_nat_usize output.val output.isLt)

theorem outputUsize_val (output : Fin 4) : (outputUsize output).val = output.val := by
  simp [outputUsize, UScalar.ofNatCore_val_eq]

/-- The same ordered row formula as the checked packed callback is a
`packedNat` raw-row instance. This reuses the established 7P bound rather
than redoing coefficient arithmetic. -/
theorem raw_formula_lt_sevenP (input : AspisR1.PoseidonExternalLocalPackedCallbackSource.Input)
    (output : Fin 4) (limb : Usize) (hlimb : limb.val < 4)
    (hlimbs : ∀ r : Fin 4,
      (AspisR1.RawPoseidonExternalRowReads.limbValue input r limb hlimb).val < P) :
    AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula
      input output limb hlimb < 7 * P := by
  let w : Fin 4 → Fin 4 → Nat := fun r _ =>
    (AspisR1.RawPoseidonExternalRowReads.limbValue input r limb hlimb).val
  have hw : ∀ r j, w r j < P := by
    intro r j
    exact hlimbs r
  have h := AspisR1.PoseidonExternalPackedAlgebra.raw_rows_lt_seven_P w hw output ⟨0, by decide⟩
  simpa [w, AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula,
    AspisR1.RawPoseidonExternalRows.rawRowNat] using h

/-- Actual from_fn success plus the exact source-order raw value now gives the
7P output-cell bound needed by the checked 44-operation recombination. The
only remaining premise is the mathematical bound for each mapped source limb. -/
theorem local_row_from_fn_bounded
    (input : AspisR1.PoseidonExternalLocalPackedCallbackSource.Input)
    (output : Fin 4)
    (hlimbs : ∀ (r : Fin 4) (limb : Usize) (hlimb : limb.val < 4),
      (AspisR1.RawPoseidonExternalRowReads.limbValue input r limb hlimb).val < P) :
    ∃ raw : Array U64 4#usize,
      ∃ index : Usize,
        index.val = output.val ∧
        array_from_fn_copy 4#usize core.marker.CopyU64
          state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
          0#u64 (input, index) = .ok raw ∧
        ∀ j : Fin 4,
          (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val < 7 * P := by
  obtain ⟨raw, hrun, hvalues⟩ :=
    AspisR1.PoseidonExternalLocalPackedCallbackSource.local_row_from_fn_success input output
  refine ⟨raw, outputUsize output, outputUsize_val output, ?_, ?_⟩
  · exact hrun
  · intro j
    rw [hvalues j]
    apply raw_formula_lt_sevenP
    intro r
    exact hlimbs r _ (by change j.val < 4; exact j.isLt)

/-- Canonical actual QM source cells discharge every mapped raw-limb bound,
so the four-row callback theorem has no free arithmetic-bound premise. -/
theorem local_row_from_fn_canonical
    (input : Array field.QM31 4#usize)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (output : Fin 4) :
    ∃ raw : Array U64 4#usize,
      array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input,
          outputUsize output) = .ok raw ∧
      ∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val < 7 * P := by
  obtain ⟨raw, index, hindex, hrun, hbound⟩ :=
    local_row_from_fn_bounded
      (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input) output
      (fun r limb hlimb =>
        AspisR1.PoseidonExternalLocalInputLimbsBound.mapped_limb_lt_P
          input hcanonical r limb hlimb)
  have hindex' : index = outputUsize output := by
    apply UScalar.eq_of_val_eq
    rw [hindex, outputUsize_val]
  have hrun' : array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input,
        outputUsize output) = .ok raw := by
    rw [← hindex']
    exact hrun
  exact ⟨raw, hrun', hbound⟩

/-- The actual from_fn row outputs retain both the raw Poseidon formula and
its `< 7P` bound, with the bound derived from canonical QM input cells. -/
theorem local_row_from_fn_canonical_full
    (input : Array field.QM31 4#usize)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt)))
    (output : Fin 4) :
    ∃ raw : Array U64 4#usize,
      array_from_fn_copy 4#usize core.marker.CopyU64
        state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
        0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input,
          outputUsize output) = .ok raw ∧
      (∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val =
          AspisR1.PoseidonExternalLocalPackedCallbackSource.rawRowFormula
            (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input)
            output (outputUsize j) (by simpa [outputUsize_val] using j.isLt)) ∧
      (∀ j : Fin 4,
        (raw.val[j.val]'(by simpa [raw.property] using j.isLt)).val < 7 * P) := by
  obtain ⟨raw0, hrun0, hvalues⟩ :=
    AspisR1.PoseidonExternalLocalPackedCallbackSource.local_row_from_fn_success
      (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input) output
  obtain ⟨raw1, hrun1, hbound⟩ :=
    local_row_from_fn_canonical input hcanonical output
  have hrun0' : array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_local_packed_raw.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (AspisR1.PoseidonExternalLocalInputLimbsBound.mappedRows input,
        outputUsize output) = .ok raw0 := hrun0
  have heq : raw0 = raw1 := by
    exact Result.ok.inj (hrun0'.symm.trans hrun1)
  refine ⟨raw0, hrun0', hvalues, ?_⟩
  intro j
  rw [heq]
  exact hbound j

#print axioms raw_formula_lt_sevenP
#print axioms local_row_from_fn_bounded
#print axioms local_row_from_fn_canonical
#print axioms local_row_from_fn_canonical_full
end AspisR1.PoseidonExternalLocalPackedBoundedRows
