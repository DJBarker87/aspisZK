import JFr_TX2_DotBounds
import NEG_MachineProduct
import NEG_DotDomain
set_option autoImplicit false
noncomputable section
namespace NEV_DotScalar
open Aeneas Aeneas.Std Result AspisR1
/-- Exact actual widened primitive, not a newly chosen product specification.
The retained checked-product law and NEG abstraction discharge the log. -/
theorem product (a b : U32) (ha : a.val<NEG_DotDomain.P) (hb : b.val<NEG_DotDomain.P) :
    ∃ out : U64,
    (core.convert.num.FromU64U32.from a)*(core.convert.num.FromU64U32.from b)=ok out ∧
    out.val=a.val*b.val ∧ out.val≤NEG_DotDomain.B ∧
    NEG_ProductAbstraction.Product 64 a.val b.val out.val := by
  let x:=core.convert.num.FromU64U32.from a
  let y:=core.convert.num.FromU64U32.from b
  have xv : x.val=a.val := by scalar_tac
  have yv : y.val=b.val := by scalar_tac
  have bounded:=NEG_DotDomain.instantiate a.val b.val ha hb
  have small : a.val*b.val<2^64 := by
    have cap : NEG_DotDomain.B<2^64 := by decide
    omega
  have native:=JFr_TX2_DotBounds.mul x y (by rw [xv];exact ha) (by rw [yv];exact hb)
  have natural:=NEG_MachineProduct.u64_value x y
  have value : (UScalar.wrapping_mul x y).val=a.val*b.val := by
    unfold NEG_ProductAbstraction.Product at natural
    rw [xv,yv,Nat.mod_eq_of_lt small] at natural
    exact natural
  refine ⟨UScalar.wrapping_mul x y,native,value,?_,?_⟩
  · rw [value];exact bounded
  · simpa only [xv,yv] using natural
#print axioms product
end NEV_DotScalar
end
