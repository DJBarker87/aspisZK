-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_NBQ_QueryBounds
set_option autoImplicit false
namespace NBQ_RawCell
open Aeneas Aeneas.Std Result

def productAdd (sum : U64) (x y : U32) : Result U64 := do
  let a ← lift (core.convert.num.FromU64U32.from x)
  let b ← lift (core.convert.num.FromU64U32.from y)
  let product ← a*b
  sum+product
/-- The exact checked operators from the emitted native cell; multiplication
is discharged symbolically in Lean, never by a native/Kani arithmetic gate. -/
theorem arithmetic (sum : U64) (x y : U32) (k : Nat) (hk : k<4)
    (hs : sum.val≤k*4611686009837453316)
    (hx : x.val<2147483647) (hy : y.val<2147483647) :
    ∃ z, productAdd sum x y=ok z ∧ z.val=sum.val+x.val*y.val ∧
      z.val≤(k+1)*4611686009837453316 := by
  have product := NBQ_QueryBounds.product x.val y.val hx hy
  have bounds := NBQ_QueryBounds.group_bound sum.val (x.val*y.val) k hk hs product
  let a : U64 := UScalar.cast .U64 x
  let b : U64 := UScalar.cast .U64 y
  have av : a.val=x.val := by scalar_tac
  have bv : b.val=y.val := by scalar_tac
  obtain ⟨p,hm,hp⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=a) (y:=b) (by
    simp only [UScalar.max_UScalarTy_U64_eq,U64.max_eq]
    rw [av,bv];omega))
  obtain ⟨z,ha,hz⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=sum) (y:=p) (by
    simp only [UScalar.max_UScalarTy_U64_eq,U64.max_eq]
    rw [hp,av,bv];omega))
  refine ⟨z,?_,?_,?_⟩
  · simp only [productAdd,lift,bind_tc_ok]
    change (do let p ← a*b;sum+p)=ok z
    rw [hm,bind_tc_ok,ha]
  · rw [hz,hp,av,bv]
  · rw [hz,hp,av,bv];exact bounds.1

#print axioms arithmetic
end NBQ_RawCell
