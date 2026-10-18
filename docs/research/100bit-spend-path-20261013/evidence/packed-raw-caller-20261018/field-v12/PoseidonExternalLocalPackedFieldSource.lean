import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalPackedRawFullSource
import PoseidonExternalLocalPackedInputDecode
import PoseidonRawLimbReassembly
import PoseidonExternalPackedAlgebra
import RawPoseidonRowField
import RawPoseidonExternalRowReads
import PoseidonInternalAccumulatorModel
import PoseidonInternalStateWords
import ExtractedMaskTowerAdd
import R0P.Poseidon

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalLocalPackedFieldSource
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalPackedRawFullSource
open AspisR1.PoseidonExternalLocalInputLimbsBound
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
open AspisR1.PoseidonExternalPackedAlgebra
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonRowField
open AspisR1.PoseidonInternalStateWords
open AspisV8R15.ExactTowerBase (P)

abbrev QMInput := Array field.QM31 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

open AspisR1.PoseidonExternalLocalPackedInputDecode

theorem external_local_packed_source_success (input : QMInput)
    (hcanonical : ∀ i : Fin 4,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (input.val[i.val]'(by simpa [input.property] using i.isLt))) :
    ∃ q : field.QM31,
      state_only_poseidon.external_local_packed input = .ok q ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM q ∧
      Decode q = R0P.poseidonPackingFormula iBasis uBasis
        (R0P.poseidonMat4 (fun r => Decode (inputCell input r))) := by
  obtain ⟨raw, hrawRun, hrawValues⟩ :=
    AspisR1.PoseidonExternalLocalPackedRawFullSource.external_local_packed_raw_source_success
      input hcanonical
  obtain ⟨q, hconvert, hqcanonical, hqdecode⟩ :=
    AspisR1.PoseidonRawLimbReassembly.source_success raw
  have hinputBound : ∀ r j, inputWord input r j < P := by
    intro r j
    exact AspisR1.PoseidonExternalLocalInputLimbsBound.mapped_limb_lt_P
      input hcanonical r (outputUsize j) (by simpa [outputUsize_val] using j.isLt)
  have hmodel := packed_raw_rows_decode (inputWord input) hinputBound
  have hsourceWords : sourceRawWord input =
      (fun r j => AspisR1.RawPoseidonExternalRows.rawRowNat
        (fun i => inputWord input i j) r) := by
    funext r j
    rfl
  have hpackedValues : (fun j =>
      (AspisR1.RawPoseidonExtensionWords.limbAt raw j).val) =
      (fun j => packedNat (7 * P) (sourceRawWord input) j) := by
    funext j
    simpa only [AspisR1.RawPoseidonExtensionWords.limbAt] using hrawValues j
  have hdecoded : Decode q =
      R0P.poseidonPackingFormula iBasis uBasis
        (R0P.poseidonMat4 (fun r => Decode (inputCell input r))) := by
    rw [hpackedValues] at hqdecode
    rw [hsourceWords] at hqdecode
    calc
      Decode q = decodeWords (fun j =>
          packedNat (7 * P)
            (fun r k => AspisR1.RawPoseidonExternalRows.rawRowNat
              (fun i => inputWord input i k) r) j) := hqdecode
      _ = R0P.poseidonPackingFormula iBasis uBasis
          (R0P.poseidonMat4 (fun r => decodeWords (fun j => inputWord input r j))) := hmodel
      _ = R0P.poseidonPackingFormula iBasis uBasis
          (R0P.poseidonMat4 (fun r => Decode (inputCell input r))) := by
        exact congrArg
          (fun values : Fin 4 → AspisV8R15.ExactTowerBase.QM31Exact =>
            R0P.poseidonPackingFormula iBasis uBasis (R0P.poseidonMat4 values))
          (funext (fun r => input_words_decode input r))
  refine ⟨q, ?_, hqcanonical, hdecoded⟩
  unfold state_only_poseidon.external_local_packed
  simp only [hrawRun, bind_tc_ok, hconvert]

#print axioms external_local_packed_source_success
end AspisR1.PoseidonExternalLocalPackedFieldSource
