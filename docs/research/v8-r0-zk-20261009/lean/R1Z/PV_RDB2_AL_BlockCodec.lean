import R1Z.PV_RDB2_CBL_GenericArrayPower
open Aeneas Aeneas.Std
namespace R1Z.PV_AL_BlockCodec
open PV_CBL_GenericArrayPower
set_option autoImplicit false

def encode : (k : Nat) → List U8 → Storage U8 k
  | 0,xs => ⟨Array.make 0#usize [],Array.make 0#usize [],xs.headD 0#u8⟩
  | k+1,xs => ⟨encode k (xs.take (2^k)),encode k (xs.drop (2^k)),()⟩

theorem flatten_encode (k : Nat) (xs : List U8) (h : xs.length=2^k) :
    flatten k (encode k xs)=xs := by
  induction k generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons x tail =>
      have ht : tail=[] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst tail
      rfl
  | succ k ih =>
    have hn : xs.length=2^k+2^k := by simpa only [Nat.pow_succ,Nat.mul_two] using h
    have hl : (xs.take (2^k)).length=2^k := by
      rw [List.length_take,Nat.min_eq_left (by omega)]
    have hr : (xs.drop (2^k)).length=2^k := by rw [List.length_drop,hn]; omega
    simp only [encode,flatten,PV_CBL_GenericArrayFlatten.even,ih _ hl,ih _ hr]
    exact List.take_append_drop _ _

#print axioms encode
#print axioms flatten_encode
end R1Z.PV_AL_BlockCodec
