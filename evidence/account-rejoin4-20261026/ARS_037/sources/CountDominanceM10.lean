import AbstractStageSpecM10

set_option autoImplicit false
namespace AspisR1.CountDominanceM10

theorem bound (n a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    n ≤ (n+1)*a*b*c :=
  (Nat.le_succ n).trans ((Nat.le_mul_of_pos_right (n+1) ha).trans
    ((Nat.le_mul_of_pos_right ((n+1)*a) hb).trans
      (Nat.le_mul_of_pos_right (((n+1)*a)*b) hc)))

#print axioms bound
end AspisR1.CountDominanceM10
