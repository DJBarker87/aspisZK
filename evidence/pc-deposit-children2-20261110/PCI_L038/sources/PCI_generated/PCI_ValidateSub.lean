import PCI_ValidateField
set_option autoImplicit false
namespace PCI_ValidateSub

theorem minus_one_nat (p x : Nat) (positive : 0<p) (bound : x<p) :
    (x+p-1)%p = if x=0 then p-1 else x-1 := by
  by_cases hz : x=0
  · subst x
    simp only [Nat.zero_add,ite_true]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [if_neg hz]
    have he : x+p-1=p+(x-1) := by omega
    rw [he,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)

theorem one_minus_nat (p x : Nat) (positive : 1<p) (bound : x<p) :
    (1+p-x)%p = if x≤1 then 1-x else p+1-x := by
  by_cases hz : x=0
  · subst x
    simp only [Nat.sub_zero,Nat.zero_le,ite_true]
    rw [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
    exact Nat.mod_eq_of_lt positive
  · by_cases ho : x=1
    · subst x
      have he : 1+p-1=p := by omega
      rw [he,Nat.mod_self]
      simp
    · rw [if_neg (by omega)]
      have he : 1+p-x=p+1-x := by omega
      rw [he,Nat.mod_eq_of_lt (by omega)]

theorem sub_one (x : UInt32) (h : x.toNat<2147483647) :
    PCC.fieldSub x 1=UInt32.ofNat (if x.toNat=0 then 2147483646 else x.toNat-1) := by
  change UInt32.ofNat ((x.toNat+2147483647-1)%2147483647)=_
  rw [minus_one_nat 2147483647 x.toNat (by decide) h]

theorem one_sub (x : UInt32) (h : x.toNat<2147483647) :
    PCC.fieldSub 1 x=UInt32.ofNat (if x.toNat≤1 then 1-x.toNat else 2147483648-x.toNat) := by
  change UInt32.ofNat ((1+2147483647-x.toNat)%2147483647)=_
  rw [one_minus_nat 2147483647 x.toNat (by decide) h]

#print axioms minus_one_nat
#print axioms one_minus_nat
#print axioms sub_one
#print axioms one_sub
end PCI_ValidateSub
