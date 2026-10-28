import NCP_DecodeTypes
set_option autoImplicit false
noncomputable section
namespace NCP_DecodeCase8
open Aeneas Aeneas.Std Result NCP_DecodeReference

theorem result (b : Array U8 32#usize)
    (h0 : NBP_DecodeWord.word b 0 < NBP_DecodeWord.P)
    (h1 : NBP_DecodeWord.word b 1 < NBP_DecodeWord.P)
    (h2 : NBP_DecodeWord.word b 2 < NBP_DecodeWord.P)
    (h3 : NBP_DecodeWord.word b 3 < NBP_DecodeWord.P)
    (h4 : NBP_DecodeWord.word b 4 < NBP_DecodeWord.P)
    (h5 : NBP_DecodeWord.word b 5 < NBP_DecodeWord.P)
    (h6 : NBP_DecodeWord.word b 6 < NBP_DecodeWord.P)
    (h7 : NBP_DecodeWord.word b 7 < NBP_DecodeWord.P)
    : reference b = ok (core.result.Result.Ok (NBG_WideBytes.limbs b)) := by
  have len : b.val.length = 32 := by simpa using b.property
  simp [NBP_DecodeWord.word,NBG_WideBytes.word,NBP_DecodeWord.P,len] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [reference,NCP_Extracted2.NCP_digest.NCP_ref_decode,
    Array.index_usize,Array.length,b.property,lift,bind_tc_ok,
    not_le.mpr h0,not_le.mpr h1,not_le.mpr h2,not_le.mpr h3,not_le.mpr h4,not_le.mpr h5,not_le.mpr h6,not_le.mpr h7,len,NBG_WideBytes.limbs,NBG_WideBytes.word,transport,error]

#print axioms result
end NCP_DecodeCase8
