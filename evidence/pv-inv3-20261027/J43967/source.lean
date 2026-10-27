import R1Z.PV_Inv_MaskBit
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskFold

def bits (initial : Nat) (xs : List Nat) : Nat :=
  xs.foldl (fun acc bit => acc ||| 2^bit) initial

theorem test_bit (initial : Nat) (xs : List Nat) (query : Nat) :
    (bits initial xs).testBit query =
      (initial.testBit query || xs.any (fun bit => decide (bit=query))) := by
  induction xs generalizing initial with
  | nil => simp [bits]
  | cons x xs ih =>
    change (bits (initial ||| 2^x) xs).testBit query = _
    rw [ih,PV_Inv_MaskBit.insert_bit]
    simp only [List.any_cons,Bool.or_assoc]

/-- Any two enumeration/dedup orders with the same member bits give the same
observable mask bit, including duplicate endpoints on a shared row. -/
theorem order_irrelevant (initial query : Nat) (xs ys : List Nat)
    (members : ∀ bit, bit ∈ xs ↔ bit ∈ ys) :
    (bits initial xs).testBit query = (bits initial ys).testBit query := by
  rw [test_bit,test_bit]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨bit,hb,he⟩;exact ⟨bit,(members bit).mp hb,he⟩
  · rintro ⟨bit,hb,he⟩;exact ⟨bit,(members bit).mpr hb,he⟩

#print axioms test_bit
#print axioms order_irrelevant
end R1Z.PV_Inv_MaskFold
