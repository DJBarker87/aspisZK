import AspisR1CuRho.Funs
import ExtractedCurrentReducer
import CuSavingsResidues

/-! First source execution bridge for the freshly extracted rho implementation.
The reducer body is identified with the already verified current reducer;
new multiply/add steps carry their explicit no-overflow proof. The enclosing
Vec/array/iterator push loop is a separate obligation. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoScalar
open Aeneas Aeneas.Std Result
open AspisV8R17.RawReducer
open AspisR1.CuSavingsResidues
open AspisR1.ExtractedCurrentReducerOps

theorem reducer_eq (x : U64) :
    AspisR1CuRho.field.reduce_u64 x =
      AspisR1Qm31ArithmeticProbe.field.reduce_u64 x := by
  simp only [AspisR1CuRho.field.reduce_u64, AspisR1CuRho.field.P,
    AspisR1Qm31ArithmeticProbe.field.reduce_u64, AspisR1Qm31ArithmeticProbe.field.P]

theorem reducer_mod (x : U64) :
    ∃ z : U32, AspisR1CuRho.field.M31.reduce_u64 x = .ok z ∧
      z.val = x.val % P ∧ z.val < P := by
  obtain ⟨z, hr, hm, hc⟩ := AspisR1.ExtractedCurrentReducer.current_reduce_mod x
  refine ⟨z, ?_, hm, hc⟩
  simp only [AspisR1CuRho.field.M31.reduce_u64, reducer_eq, hr, bind_tc_ok]

/-- The scalar operation sequence in push_loop0.body, after its array reads.
Both casts are exact widenings and both checked arithmetic operations succeed.
It is not a replacement assumption about the full loop. -/
def addProduct (raw : U64) (power basis : U32) : Result U64 := do
  let product ← UScalar.mul (UScalar.cast .U64 power) (UScalar.cast .U64 basis)
  UScalar.add raw product

theorem addProduct_success (raw : U64) (power basis : U32) (count : Nat)
    (hr : RhoBound raw.val count) (hp : power.val < P) (hb : basis.val < P) :
    ∃ out : U64, addProduct raw power basis = .ok out ∧
      out.val = raw.val + power.val*basis.val := by
  have hprod := canonical_product_bound power.val basis.val hp hb
  have hfit := rho_add_fits raw.val count (power.val*basis.val) hr hprod
  have hpower := AspisR1.ExtractedCurrentReducer.cast_widen_value power
  have hbasis := AspisR1.ExtractedCurrentReducer.cast_widen_value basis
  have hmul : (UScalar.cast .U64 power).val * (UScalar.cast .U64 basis).val < 2^64 := by
    rw [hpower,hbasis]
    omega
  obtain ⟨product,hm,hv⟩ := mul_success _ _ hmul
  rw [hpower,hbasis] at hv
  obtain ⟨out,ha,hov⟩ := add_success raw product (by rw [hv]; exact hfit)
  refine ⟨out,?_,?_⟩
  · simp only [addProduct,hm,ha,bind_tc_ok]
  · simpa only [hv] using hov

theorem source_flush_condition (count : Usize) :
    (UScalar.and count 3#usize).val = count.val % 4 := by
  rw [and_value]
  change count.val &&& 3 = count.val % 4
  exact mask_low_eq_mod count.val 2

#print axioms reducer_eq
#print axioms reducer_mod
#print axioms addProduct_success
#print axioms source_flush_condition
end AspisR1.CuSavingsRhoScalar
