import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalLocalInputLimbsBoundV12
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
namespace AspisR1.PoseidonExternalLocalPackedInputDecode
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLocalInputLimbsBound
open AspisR1.PoseidonExternalPackedAlgebra
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonRowField
open AspisR1.PoseidonInternalStateWords
open AspisV8R15.ExactTowerBase (P)

abbrev QMInput := Array field.QM31 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

def inputCell (input : QMInput) (r : Fin 4) : field.QM31 :=
  input.val[r.val]'(by simpa [input.property] using r.isLt)

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

def outputUsize (j : Fin 4) : Usize :=
  Usize.ofNatCore j.val (small_nat_usize j.val j.isLt)

theorem outputUsize_val (j : Fin 4) : (outputUsize j).val = j.val := by
  simp [outputUsize, UScalar.ofNatCore_val_eq]

def inputWord (input : QMInput) (r j : Fin 4) : Nat :=
  (limbValue (mappedRows input) r (outputUsize j)
    (by simpa [outputUsize_val] using j.isLt)).val

theorem input_words_decode (input : QMInput) (r : Fin 4) :
    decodeWords (fun j => inputWord input r j) = Decode (inputCell input r) := by
  have hrow : rowValue (mappedRows input) r = wordVec (inputCell input r) := by
    simp [rowValue, mappedRows, limbsOf, inputCell, wordVec]
  have hwords : (fun j => inputWord input r j) =
      (fun j => (AspisR1.PoseidonFullRoundCellStep.cell
        (wordVec (inputCell input r)) j).val) := by
    funext j
    simp [inputWord, limbValue, hrow, outputUsize_val,
      AspisR1.PoseidonFullRoundCellStep.cell]
  rw [hwords]
  exact AspisR1.PoseidonInternalAccumulatorModel.wordVec_decode (inputCell input r)

#print axioms input_words_decode
end AspisR1.PoseidonExternalLocalPackedInputDecode
