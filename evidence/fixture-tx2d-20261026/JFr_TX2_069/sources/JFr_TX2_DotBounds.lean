import FIo_ScalarBridge
set_option autoImplicit false
namespace AspisR1.JFr_TX2_DotBounds
open Aeneas Aeneas.Std Result

def P : Nat := 2147483647

/-- Each native inner batch has at most four products. This explicit bound
explains why kernel evaluation of a whole dot recurrence is unnecessary. -/
theorem four_products (a b n s : Nat) (ha : a<P) (hb : b<P)
    (hn : n<4) (hs : s≤n*((P-1)*(P-1))) : s+a*b<2^64 := by
  have hp : a*b≤(P-1)*(P-1) := Nat.mul_le_mul (by omega) (by omega)
  have hsum : s+a*b≤(n+1)*((P-1)*(P-1)) := by nlinarith
  have hfour : (n+1)*((P-1)*(P-1))≤4*((P-1)*(P-1)) :=
    Nat.mul_le_mul_right _ (by omega)
  norm_num [P] at hsum hfour ⊢
  omega

theorem mul (a b : U64) (ha : a.val<P) (hb : b.val<P) :
    a*b=ok (UScalar.wrapping_mul a b) := by
  apply FIo_ScalarBridge.mul
  have h := four_products a.val b.val 0 0 ha hb (by omega) (by omega)
  norm_num [UScalar.size,U64.size] at h ⊢
  exact h

theorem add_product (a b s : U64) (n : Nat) (ha : a.val<P) (hb : b.val<P)
    (hn : n<4) (hs : s.val≤n*((P-1)*(P-1))) :
    ∃ product out, a*b=ok product ∧ s+product=ok out ∧
      out.val=s.val+a.val*b.val ∧ out.val≤(n+1)*((P-1)*(P-1)) := by
  have hpBound : a.val*b.val<2^64 := by simpa only [Nat.zero_add] using four_products _ _ 0 0 ha hb (by omega) (by omega)
  obtain ⟨product,hp,vp⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b)
    (by norm_num [UScalar.max,UScalar.size,U64.max,U64.size];norm_num at hpBound;omega))
  have total := four_products a.val b.val n s.val ha hb hn hs
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=s) (y:=product)
    (by rw [vp];norm_num [UScalar.max,UScalar.size,U64.max,U64.size];norm_num at total;omega))
  refine ⟨product,out,hp,ho,?_,?_⟩
  · rw [vo,vp]
  · have hpSmall : a.val*b.val≤(P-1)*(P-1) := Nat.mul_le_mul (by omega) (by omega)
    rw [vo,vp]
    nlinarith

#print axioms four_products
#print axioms mul
#print axioms add_product
end AspisR1.JFr_TX2_DotBounds
