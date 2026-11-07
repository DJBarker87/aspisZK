import PCF_DigestFirst
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_FirstStub

theorem low_byte (a : U32) :
    (core.num.U32.to_le_bytes a).val[0]! = UScalar.cast .U8 a := by
  unfold core.num.U32.to_le_bytes
  rw [BitVec.toLEBytes.eq_1]
  rfl

theorem first_reply (a b c d e f g h : U32) :
    AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.first_canonical_byte
      (PCF_DigestFirst.words a b c d e f g h) = ok (UScalar.cast .U8 a) := by
  rw [PCF_ChildLaws.first, PCF_DigestFirst.first_words, low_byte]

#print axioms low_byte
#print axioms first_reply
end PCF_FirstStub
