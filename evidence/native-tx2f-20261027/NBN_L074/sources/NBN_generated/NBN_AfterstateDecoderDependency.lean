import NBN_AfterDecodeParent
set_option autoImplicit false
noncomputable section
namespace NBN_AfterstateDecoderDependency
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Decode := NBN_AfterDecodeTypes.Decode
abbrev NBN_Dep_DigestDecode := NBN_AfterDecodeTypes.NBN_Dep_DigestDecode
abbrev run := NBN_AfterDecodeParent.run

theorem source (decode : Decode) (lower : NBN_Dep_DigestDecode decode) (bytes : Slice U8) :
    run decode bytes = pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1 bytes :=
  NBN_AfterDecodeParent.source decode lower bytes

#print axioms source
end NBN_AfterstateDecoderDependency
