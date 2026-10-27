import ProverRwSampler.Funs
import ExtractedQM31SamplerCorrect

/-! Bounded wrapping/checked arithmetic bridge for the selected sampler.
The generated input has one explicitly receipted shift-numeral API adaptation.
No oracle, sampler-distribution, or whole-prover conclusion is asserted here. -/
set_option autoImplicit false
namespace R1Z.ProverRwSamplerArithmetic
open Aeneas Aeneas.Std Result ControlFlow WP

 theorem add_exact (x y : Usize) (h : x.val + y.val ≤ Usize.max) :
    x + y = ok (Usize.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := spec_imp_exists (Usize.add_spec (x := x) (y := y) h)
  have he : z = Usize.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt (by
      simpa only [UScalar.size, UScalarTy.numBits, Usize.numBits] using
        (show x.val + y.val < 2^Usize.numBits from by
          have hp : 0 < 2^Usize.numBits := by positivity
          rw [Usize.max] at h
          omega))]
    exact hv
  simpa only [he] using hz

 theorem mul_exact (x y : Usize) (h : x.val * y.val ≤ Usize.max) :
    x * y = ok (Usize.wrapping_mul x y) := by
  obtain ⟨z,hz,hv⟩ := spec_imp_exists (Usize.mul_spec (x := x) (y := y) h)
  have he : z = Usize.wrapping_mul x y := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt (by
      simpa only [UScalar.size, UScalarTy.numBits, Usize.numBits] using
        (show x.val * y.val < 2^Usize.numBits from by
          have hp : 0 < 2^Usize.numBits := by positivity
          rw [Usize.max] at h
          omega))]
    exact hv
  simpa only [he] using hz

 theorem sub_exact (x y : Usize) (h : y.val ≤ x.val) :
    x - y = ok (Usize.wrapping_sub x y) := by
  obtain ⟨z,hz,hv⟩ := spec_imp_exists (Usize.sub_spec (x := x) (y := y) h)
  have he : z = Usize.wrapping_sub x y := by
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_sub_val_eq]
    have hx : x.val < UScalar.size .Usize := by simpa only [UScalar.val, UScalar.size, UScalarTy.numBits] using x.bv.isLt
    have hy : y.val < UScalar.size .Usize := by simpa only [UScalar.val, UScalar.size, UScalarTy.numBits] using y.bv.isLt
    rw [show x.val + (UScalar.size .Usize - y.val) =
      (x.val - y.val) + UScalar.size .Usize from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    exact hv.1
  simpa only [he] using hz

 theorem shift_exact (r : U64) :
    r <<< 32#i32 = ok (U64.wrapping_shl r 32#u32) := by
  obtain ⟨s,hs,hv,hbv⟩ := spec_imp_exists
    (U64.ShiftLeft_IScalar_spec r (32#i32) (by decide) (by decide))
  have he : s = U64.wrapping_shl r 32#u32 := by
    have he : s.bv = (U64.wrapping_shl r 32#u32).bv := by
      simpa only [U64.wrapping_shl_bv_eq, BitVec.shiftLeft_eq,
        show (32#u32).val = 32 from rfl,
        show (32#i32).toNat = 32 from rfl,
        show 32 % 64 = 32 from rfl] using hbv
    exact congrArg (fun bv : BitVec 64 => (⟨bv⟩ : U64)) he
  simpa only [he] using hs

#print axioms add_exact
#print axioms mul_exact
#print axioms sub_exact
#print axioms shift_exact
end R1Z.ProverRwSamplerArithmetic
