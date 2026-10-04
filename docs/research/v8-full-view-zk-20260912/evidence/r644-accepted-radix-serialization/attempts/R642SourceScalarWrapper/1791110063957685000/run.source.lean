import AspisV8R19.R623PackedDecoderExecution
import AspisV8R19.R637PackedBitExtraction
import Mathlib.Tactic
set_option autoImplicit false
namespace AspisV8R19.R642SourceScalarWrapper
open Aeneas Aeneas.Std

#check BitVec.setWidth_ofNat_of_le_of_lt
#check BitVec.setWidth_ofNat_of_le
#check BitVec.setWidth_ofNat
#check BitVec.setWidth_eq_append_extractLsb'
#print UScalar.cast
#print UScalar.and
lemma source_mask_cast_bv (w : U64) :
    (R624DecoderInnerExecution.sourceMaskedValue w).bv =
      BitVec.extractLsb' 0 32 (w.bv &&& (2147483647 : BitVec 64)) := by
  simp only [R624DecoderInnerExecution.sourceMaskedValue, UScalar.cast, UScalar.and]

end AspisV8R19.R642SourceScalarWrapper
