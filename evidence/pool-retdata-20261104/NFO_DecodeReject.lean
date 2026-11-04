import NFO_RawDecode
set_option autoImplicit false
namespace NFO_DecodeReject
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

theorem wrong_length (bytes : Slice U8) (different : bytes.val.length ≠ 792) :
    NFO_RawDecode.decode bytes = ok (.Err pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  have ne : Slice.len bytes ≠ 792#usize := by
    intro eq
    apply different
    exact congrArg UScalar.val eq
  have unequal : (Slice.len bytes != 792#usize) = true := by simp [ne]
  simp only [NFO_RawDecode.decode, unequal, ↓reduceIte]
#print axioms wrong_length
end NFO_DecodeReject
