import S6NativeAfterstateDecoderFactoredV1
set_option autoImplicit false
noncomputable section
namespace NBN_AfterDecodeTypes
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Digest := Array U32 8#usize
abbrev Decode := Array U8 32#usize → Result (core.result.Result Digest atomic_statement.AtomicStatementError)
def NBN_Dep_DigestDecode (decode : Decode) : Prop :=
  ∀ bytes, decode bytes = atomic_statement.decode_digest_canonical bytes
end NBN_AfterDecodeTypes
