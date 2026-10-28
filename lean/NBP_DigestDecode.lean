import NBP_DecodeWord
import NBP_Decode1
import NBP_Decode2
import NBP_Decode3
import NBP_Decode4
import NBP_Decode5
import NBP_Decode6
import NBP_Decode7
import NBP_DecodeSuccess
set_option autoImplicit false
noncomputable section
namespace NBP_DigestDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder NBP_DecodeWord
/-- Source order, including all noncanonical rejections. -/
def decoded (bytes : Array U8 32#usize) :
    core.result.Result (Array U32 8#usize) atomic_statement.AtomicStatementError :=
  if word bytes 0 >= P then .Err .NonCanonicalDigest else
  if word bytes 1 >= P then .Err .NonCanonicalDigest else
  if word bytes 2 >= P then .Err .NonCanonicalDigest else
  if word bytes 3 >= P then .Err .NonCanonicalDigest else
  if word bytes 4 >= P then .Err .NonCanonicalDigest else
  if word bytes 5 >= P then .Err .NonCanonicalDigest else
  if word bytes 6 >= P then .Err .NonCanonicalDigest else
  if word bytes 7 >= P then .Err .NonCanonicalDigest else
  .Ok (NBG_WideBytes.limbs bytes)

theorem result (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes = ok (decoded bytes) := by
  by_cases h0 : word bytes 0 >= P
  · simpa [decoded,h0,if_pos] using NBP_DecodeWord.reject0 bytes h0
  ·
    by_cases h1 : word bytes 1 >= P
    · simpa [decoded,h0,if_neg,h1,if_pos] using NBP_Decode1.result bytes (lt_of_not_ge h0) h1
    ·
      by_cases h2 : word bytes 2 >= P
      · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_pos] using NBP_Decode2.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) h2
      ·
        by_cases h3 : word bytes 3 >= P
        · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_pos] using NBP_Decode3.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) h3
        ·
          by_cases h4 : word bytes 4 >= P
          · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_pos] using NBP_Decode4.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) h4
          ·
            by_cases h5 : word bytes 5 >= P
            · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_pos] using NBP_Decode5.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) h5
            ·
              by_cases h6 : word bytes 6 >= P
              · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_pos] using NBP_Decode6.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) h6
              ·
                by_cases h7 : word bytes 7 >= P
                · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_neg,h7,if_pos] using NBP_Decode7.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) h7
                · simpa [decoded,h0,if_neg,h1,if_neg,h2,if_neg,h3,if_neg,h4,if_neg,h5,if_neg,h6,if_neg,h7,if_neg] using NBP_DecodeSuccess.result bytes (lt_of_not_ge h0) (lt_of_not_ge h1) (lt_of_not_ge h2) (lt_of_not_ge h3) (lt_of_not_ge h4) (lt_of_not_ge h5) (lt_of_not_ge h6) (lt_of_not_ge h7)

#print axioms result
end NBP_DigestDecode
