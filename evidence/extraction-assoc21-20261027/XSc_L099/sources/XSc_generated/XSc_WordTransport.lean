import XSc_RecordFieldTypes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_WordTransport
/-- Symbolic four-byte bridge needed by the old aggregate decoder carrier. -/
theorem source (a b c d : U8) :
 core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])=XRn_Join_word [a,b,c,d] := by
 have ha : a.val<256 := by scalar_tac
 have hb : b.val<256 := by scalar_tac
 have hc : c.val<256 := by scalar_tac
 have hd : d.val<256 := by scalar_tac
 have join (lo hi : Nat) (small : lo<256) : lo ||| hi <<< 8=lo+256*hi := by
  have small' : lo<2^8 := small
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt small',Nat.shiftLeft_eq]
  change hi*256+lo=lo+256*hi
  omega
 have hd8 : d.val <<< 8<65536 := by rw [Nat.shiftLeft_eq]; omega
 have hd24 : d.val <<< 8<16777216 := by omega
 have hcd : (c.val+256*d.val) <<< 8<16777216 := by rw [Nat.shiftLeft_eq]; omega
 have hcd32 : (c.val+256*d.val) <<< 8<4294967296 := by omega
 have hbc : (b.val+256*(c.val+256*d.val)) <<< 8<4294967296 := by rw [Nat.shiftLeft_eq]; omega
 have whole : a.val+256*(b.val+256*(c.val+256*d.val))<4294967296 := by omega
 apply UScalar.eq_of_val_eq
 change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat = (XRn_Join_word [a,b,c,d]).val
 simp [BitVec.fromLEBytes,XRn_Join_word,XRn_Join_Bytes.le32]
 simp only [Nat.mod_eq_of_lt (show a.val<4294967296 by omega),
  Nat.mod_eq_of_lt (show b.val<4294967296 by omega),
  Nat.mod_eq_of_lt (show c.val<16777216 by omega),
  Nat.mod_eq_of_lt (show d.val<65536 by omega),Nat.mod_eq_of_lt hd8,Nat.mod_eq_of_lt hd24]
 rw [join c.val d.val hc]
 simp only [Nat.mod_eq_of_lt hcd,Nat.mod_eq_of_lt hcd32]
 rw [join b.val (c.val+256*d.val) hb]
 simp only [Nat.mod_eq_of_lt hbc]
 rw [join a.val (b.val+256*(c.val+256*d.val)) ha]
 exact (Nat.mod_eq_of_lt whole).symm

#print axioms source
end XSc_WordTransport
