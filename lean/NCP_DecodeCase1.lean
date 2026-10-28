import NCP_DecodeTypes
set_option autoImplicit false
noncomputable section
namespace NCP_DecodeCase1
open Aeneas Aeneas.Std Result NCP_DecodeReference

theorem result (b : Array U8 32#usize)
    (h0 : NBP_DecodeWord.word b 0 < NBP_DecodeWord.P)
    (h1 : NBP_DecodeWord.word b 1 >= NBP_DecodeWord.P)
    : reference b = ok (core.result.Result.Err AspisR1TerminalDecoder.atomic_statement.AtomicStatementError.NonCanonicalDigest) := by
  have len : b.val.length = 32 := by simpa using b.property
  simp [NBP_DecodeWord.word,NBG_WideBytes.word,NBP_DecodeWord.P,len] at h0 h1
  simp [reference,NCP_Extracted2.NCP_digest.NCP_ref_decode,
    Array.index_usize,Array.length,b.property,lift,bind_tc_ok,
    h0,h1,NBG_WideBytes.limbs,NBG_WideBytes.word,transport,error]

#print axioms result
end NCP_DecodeCase1
