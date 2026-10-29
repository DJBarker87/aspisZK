import NDE_StubWordBounds
set_option autoImplicit false
namespace NDN_ArithmeticBounds
abbrev P : Nat := 2147483647

theorem three_products (a b c d e f : Nat)
 (ha:a<P) (hb:b<P) (hc:c<P) (hd:d<P) (he:e<P) (hf:f<P) :
 a*b+c*d+e*f<2^64 := by
 have h:=Nat.mul_le_mul (show a≤P-1 by omega) (show b≤P-1 by omega)
 have i:=Nat.mul_le_mul (show c≤P-1 by omega) (show d≤P-1 by omega)
 have j:=Nat.mul_le_mul (show e≤P-1 by omega) (show f≤P-1 by omega)
 norm_num [P] at h i j ⊢
 omega

theorem four_products (a b c d e f g h : Nat)
 (ha:a<P) (hb:b<P) (hc:c<P) (hd:d<P) (he:e<P) (hf:f<P) (hg:g<P) (hh:h<P) :
 a*b+c*d+e*f+g*h<2^64 := by
 have h0:=Nat.mul_le_mul (show a≤P-1 by omega) (show b≤P-1 by omega)
 have h1:=Nat.mul_le_mul (show c≤P-1 by omega) (show d≤P-1 by omega)
 have h2:=Nat.mul_le_mul (show e≤P-1 by omega) (show f≤P-1 by omega)
 have h3:=Nat.mul_le_mul (show g≤P-1 by omega) (show h≤P-1 by omega)
 norm_num [P] at h0 h1 h2 h3 ⊢
 omega

theorem prefix_product (raw a b count : Nat) (hr:raw≤count*(P-1)^2)
 (ha:a<P) (hb:b<P) (hc:count<4) :
 raw+a*b≤(count+1)*(P-1)^2 ∧ raw+a*b<2^64 := by
 have hp:=Nat.mul_le_mul (show a≤P-1 by omega) (show b≤P-1 by omega)
 have hp2 : a*b≤(P-1)^2 := by simpa only [pow_two] using hp
 have step : raw+a*b≤(count+1)*(P-1)^2 := by
  simpa only [Nat.add_mul,one_mul] using Nat.add_le_add hr hp2
 have cap : (count+1)*(P-1)^2≤4*(P-1)^2 := Nat.mul_le_mul_right _ (by omega)
 norm_num [P] at cap ⊢
 constructor
 · exact step
 · norm_num [P] at step;omega

#print axioms three_products
#print axioms four_products
#print axioms prefix_product
end NDN_ArithmeticBounds
