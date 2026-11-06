import NJB_StubLaws
set_option autoImplicit false
namespace AspisR1.NJB_TagRaw
open Aeneas Aeneas.Std Result
abbrev B : Nat := 4611686009837453316
theorem four_products_fit : 4*B<18446744073709551616 := by decide
theorem product_bound (x y : Nat) (hx : x<2147483647) (hy : y<2147483647) : x*y≤B := by
 exact Nat.mul_le_mul (show x≤2147483646 by omega) (show y≤2147483646 by omega)
/-- Full checked integer Result supplying the native product reply. No
field multiplication is attempted by the native solver. -/
theorem product (x y : U64) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 ∃ out,U64.mul x y=ok out ∧ out.val=x.val*y.val ∧ out.val≤B := by
 have bound := product_bound x.val y.val hx hy
 obtain ⟨out,call,value⟩ := WP.spec_imp_exists (U64.mul_spec (x:=x) (y:=y) (by scalar_tac))
 exact ⟨out,call,value,by rw [value];exact bound⟩
theorem step_bound (raw product k : Nat) (hk : k<4) (hr : raw≤k*B) (hp : product≤B) :
 raw+product≤(k+1)*B ∧ raw+product<18446744073709551616 := by
 have h : raw+product≤(k+1)*B := by omega
 constructor
 · exact h
 · have h4 : (k+1)*B≤4*B := Nat.mul_le_mul_right B (by omega)
   exact lt_of_le_of_lt (le_trans h h4) four_products_fit
theorem sum_bound (terms : List Nat) (bounded : ∀ p∈terms,p≤B) : terms.sum≤terms.length*B := by
 induction terms with
 | nil => simp
 | cons p ps ih =>
   have hp := bounded p (by simp)
   have hs := ih (fun q hq=>bounded q (by simp [hq]))
   simp only [List.sum_cons,List.length_cons]
   omega
/-- The actual source's at-most-four lazy reduction invariant. -/
theorem chunk_bound (terms : List Nat) (small : terms.length≤4) (bounded : ∀ p∈terms,p≤B) :
 terms.sum<18446744073709551616 := by
 have bound := sum_bound terms bounded
 exact lt_of_le_of_lt (le_trans bound (Nat.mul_le_mul_right B small)) four_products_fit
#print product
#print axioms four_products_fit
#print axioms product_bound
#print axioms product
#print axioms step_bound
#print axioms sum_bound
#print axioms chunk_bound
end AspisR1.NJB_TagRaw
