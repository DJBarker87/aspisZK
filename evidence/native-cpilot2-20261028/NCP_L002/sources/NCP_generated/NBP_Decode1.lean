import NBP_DecodeWord
set_option autoImplicit false
noncomputable section
namespace NBP_Decode1
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_DecodeWord
theorem result (bytes : Array U8 32#usize)
    (h0 : word bytes 0 < P)
    (h1 : word bytes 1 >= P) :
    atomic_statement.decode_digest_canonical bytes = ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NBG_WideBytes.word,P,len] at h0 h1
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    bytes.property,NBG_Atomic.m31_decode,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,not_le.mpr h0,h1]
#print axioms result
end NBP_Decode1
