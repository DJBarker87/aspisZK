import XSe_ByteDecoder
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_WordValue
/-- No modulo wrap occurs when reading four actual bytes. -/
theorem four (a b c d : U8) :
 (XRn_Join_word [a,b,c,d]).val=XRn_Join_Bytes.le32 [a,b,c,d] := by
 have ha : a.val<256 := by scalar_tac
 have hb : b.val<256 := by scalar_tac
 have hc : c.val<256 := by scalar_tac
 have hd : d.val<256 := by scalar_tac
 change XRn_Join_Bytes.le32 [a,b,c,d]%4294967296=XRn_Join_Bytes.le32 [a,b,c,d]
 apply Nat.mod_eq_of_lt
 simp only [XRn_Join_Bytes.le32,List.take_succ_cons,List.take_zero,List.foldr_cons,List.foldr_nil]
 omega
theorem window (s : Slice U8) (i : Nat) (bound : i+3<s.val.length) :
 (XRn_Join_word ((s.val.drop i).take 4)).val=XRn_Join_Bytes.le32 ((s.val.drop i).take 4) := by
 rw [XSe_ByteWindows.window s i bound]
 exact four _ _ _ _
#print axioms four
#print axioms window
end XSe_WordValue
