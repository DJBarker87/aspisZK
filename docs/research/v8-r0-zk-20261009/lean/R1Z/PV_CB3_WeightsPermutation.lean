import R1Z.PV_CB3_WeightsBits
set_option autoImplicit false
namespace R1Z.PV_CB3_WeightsPermutation

def pack (a b c d e : Nat) : Nat :=
  (e <<< 8) ||| ((d <<< 6) ||| ((c <<< 4) ||| ((b <<< 2) ||| a)))

theorem pack_value (a b c d e : Nat) (ha : a < 4) (hb : b < 4) (hc : c < 4)
    (hd : d < 4) (he : e < 4) :
    pack a b c d e = a+4*b+16*c+64*d+256*e := by
  have h0 : (b <<< 2) ||| a = 4*b+a := by
    rw [←Nat.shiftLeft_add_eq_or_of_lt (by omega : a < 2^2),Nat.shiftLeft_eq]
    omega
  have h1 : (c <<< 4) ||| ((b <<< 2) ||| a) = 16*c+(4*b+a) := by
    rw [h0,←Nat.shiftLeft_add_eq_or_of_lt (by omega : 4*b+a < 2^4),Nat.shiftLeft_eq]
    omega
  have h2 : (d <<< 6) ||| ((c <<< 4) ||| ((b <<< 2) ||| a)) = 64*d+(16*c+(4*b+a)) := by
    rw [h1,←Nat.shiftLeft_add_eq_or_of_lt (by omega : 16*c+(4*b+a) < 2^6),Nat.shiftLeft_eq]
    omega
  unfold pack
  rw [h2,←Nat.shiftLeft_add_eq_or_of_lt (by omega : 64*d+(16*c+(4*b+a)) < 2^8),Nat.shiftLeft_eq]
  omega

theorem row_value (j : Nat) : PV_CB3_WeightsBits.row j = PV_CB3_WeightsDomain.row j := by
  have hpack : PV_CB3_WeightsBits.row j = pack
      (PV_CB3_WeightsBits.digit j 3) (PV_CB3_WeightsBits.digit j 4)
      (PV_CB3_WeightsBits.digit j 2) (PV_CB3_WeightsBits.digit j 0)
      (PV_CB3_WeightsBits.digit j 1) := by
    unfold PV_CB3_WeightsBits.row pack
    ac_rfl
  rw [hpack,pack_value _ _ _ _ _ (PV_CB3_WeightsBits.digit_bound _ _)
    (PV_CB3_WeightsBits.digit_bound _ _) (PV_CB3_WeightsBits.digit_bound _ _)
    (PV_CB3_WeightsBits.digit_bound _ _) (PV_CB3_WeightsBits.digit_bound _ _)]
  simp only [PV_CB3_WeightsBits.digit_value,PV_CB3_WeightsDomain.row]
  omega
#print axioms pack_value
#print axioms row_value
end R1Z.PV_CB3_WeightsPermutation
