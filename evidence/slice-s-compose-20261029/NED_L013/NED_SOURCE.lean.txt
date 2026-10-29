import NBG_WideBytes
import NBG_Atomic
set_option autoImplicit false
noncomputable section
namespace NBP_DecodeWord
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev word := NBG_WideBytes.word
abbrev P : U32 := 2147483647#u32
/-- The first rejecting word stops before any later word is decoded. -/
theorem reject0 (bytes : Array U8 32#usize) (h0 : word bytes 0 >= P) :
    atomic_statement.decode_digest_canonical bytes =
      ok (.Err .NonCanonicalDigest) := by
  have len : bytes.val.length = 32 := by simpa using bytes.property
  simp [word,NBG_WideBytes.word,P, len] at h0
  simp [atomic_statement.decode_digest_canonical,Array.index_usize,
    Array.length,bytes.property,NBG_Atomic.m31_decode,h0,
    core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame]
#print axioms reject0
end NBP_DecodeWord
