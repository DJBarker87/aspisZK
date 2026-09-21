import AspisV8R17.TranscriptAddresses

/-! Literal field order of StateOnlyHidingContext::encode. This establishes
preimage distinction, not collision resistance or R17 adapter integration. -/
set_option autoImplicit false
namespace AspisV8R17.HidingContextBytes
open AspisV8PairedCommitment AspisV8R17.TranscriptAddresses

def encode (version : Byte) (statement nonce layout factor : List Byte) : List Byte :=
  version :: (statement ++ nonce ++ layout ++ factor)

theorem encoded_length (version : Byte) (statement nonce layout factor : List Byte)
    (hs : statement.length = 32) (hn : nonce.length = 32)
    (hl : layout.length = 8) (hf : factor.length = 8) :
    (encode version statement nonce layout factor).length = 81 := by
  simp [encode, hs, hn, hl, hf]

theorem nonce_slice (version : Byte) (statement nonce layout factor : List Byte)
    (hs : statement.length = 32) (hn : nonce.length = 32) :
    ((encode version statement nonce layout factor).drop 33).take 32 = nonce := by
  simp [encode, List.drop_append, hs, hn, List.take_append]

theorem different_nonce_different_context (version : Byte)
    (statement left right layout factor : List Byte)
    (hs : statement.length = 32) (hl : left.length = 32) (hr : right.length = 32)
    (different : left ≠ right) :
    encode version statement left layout factor ≠ encode version statement right layout factor := by
  intro h
  have slices := congrArg (fun bytes : List Byte => (bytes.drop 33).take 32) h
  rw [nonce_slice version statement left layout factor hs hl,
    nonce_slice version statement right layout factor hs hr] at slices
  exact different slices

theorem different_nonce_different_absorb (state statement left right layout factor : List Byte)
    (version label : Byte) (hs : statement.length = 32)
    (hl : left.length = 32) (hr : right.length = 32) (different : left ≠ right) :
    absorbInput state label (encode version statement left layout factor) ≠
      absorbInput state label (encode version statement right layout factor) := by
  intro h
  apply different_nonce_different_context version statement left right layout factor hs hl hr different
  exact List.append_cancel_left h

#print axioms encoded_length
#print axioms nonce_slice
#print axioms different_nonce_different_context
#print axioms different_nonce_different_absorb
end AspisV8R17.HidingContextBytes
