import R1Z.ProverRwOuterEncode
set_option autoImplicit false
namespace R1Z.ProverRwOuterBytes
open Aeneas Aeneas.Std Result ProverRwOuterContext ProverRwOuterWrite ProverRwOuterEncode

def bytes (c : Context) : List U8 :=
  [1#u8] ++ c.statement_digest.val ++ c.mask_nonce.val ++
    (core.num.U64.to_le_bytes c.mask_layout_fingerprint).val ++
    (core.num.U64.to_le_bytes c.layout_factor_fingerprint).val

/-- Symbolic field concatenation, without expanding either private-sized
32-byte array or evaluating concrete fingerprint arithmetic. -/
theorem value_bytes (c : Context) : (value c).val = bytes c := by
  have hd : c.statement_digest.val.length = 32 := c.statement_digest.property
  have hn : c.mask_nonce.val.length = 32 := c.mask_nonce.property
  have hm : (core.num.U64.to_le_bytes c.mask_layout_fingerprint).val.length = 8 :=
    (core.num.U64.to_le_bytes c.mask_layout_fingerprint).property
  have hf : (core.num.U64.to_le_bytes c.layout_factor_fingerprint).val.length = 8 :=
    (core.num.U64.to_le_bytes c.layout_factor_fingerprint).property
  have d32 : c.statement_digest.val.take 32 = c.statement_digest.val := List.take_of_length_le (by omega)
  have d64 : c.statement_digest.val.take 64 = c.statement_digest.val := List.take_of_length_le (by omega)
  have d72 : c.statement_digest.val.take 72 = c.statement_digest.val := List.take_of_length_le (by omega)
  have n32 : c.mask_nonce.val.take 32 = c.mask_nonce.val := List.take_of_length_le (by omega)
  have n40 : c.mask_nonce.val.take 40 = c.mask_nonce.val := List.take_of_length_le (by omega)
  have m8 : (core.num.U64.to_le_bytes c.mask_layout_fingerprint).val.take 8 =
      (core.num.U64.to_le_bytes c.mask_layout_fingerprint).val := List.take_of_length_le (by omega)
  have f8 : (core.num.U64.to_le_bytes c.layout_factor_fingerprint).val.take 8 =
      (core.num.U64.to_le_bytes c.layout_factor_fingerprint).val := List.take_of_length_le (by omega)
  simp [value,put,initial,Array.set,Array.repeat,List.setSlice!,bytes,
    hd,hn,hm,hf,List.take_append,List.drop_append,d32,d64,d72,n32,n40,m8,f8]

#print axioms value_bytes
end R1Z.ProverRwOuterBytes
