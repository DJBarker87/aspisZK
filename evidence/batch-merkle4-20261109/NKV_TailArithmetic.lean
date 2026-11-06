import NKV_BatchGeometry
import NKL_TailGeometry
set_option autoImplicit false
namespace NKV_TailArithmetic
open Aeneas Aeneas.Std Result

theorem scaled_value (count : Usize) (bound : count.val≤172) :
 (Usize.wrapping_mul 32#usize count).val=32*count.val := by
 rw [Usize.wrapping_mul_val_eq]
 have thirtytwo : (32#usize).val=32 := by scalar_tac
 rw [thirtytwo]
 apply Nat.mod_eq_of_lt
 have cap : 5504<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 omega

theorem checked_scale (count : Usize) (bound : count.val≤172) :
 (32#usize*count : Result Usize)=ok (Usize.wrapping_mul 32#usize count) := by
 have capacity : 5504≤Usize.max := by scalar_tac
 have thirtytwo : (32#usize).val=32 := by scalar_tac
 have spec : WP.spec (32#usize*count : Result Usize) (fun out => out.val=32*count.val) := by
   apply UScalar.mul_spec
   simpa only [UScalar.max_USize_eq,thirtytwo] using
     (show 32*count.val≤5504 by omega).trans capacity
 obtain ⟨out,run,value⟩:=WP.spec_imp_exists spec
 have same : out=Usize.wrapping_mul 32#usize count :=
   UScalar.eq_of_val_eq (value.trans (scaled_value count bound).symm)
 exact run.trans (congrArg Result.ok same)

theorem fits (slot count : Nat) (s : slot<6) (bound : count≤NKL_TailGeometry.capacity slot) :
 32*count≤5504 ∧ 32*count≤9216 ∧
 32*count≤32*NKL_TailGeometry.capacity slot ∧
 (32*NKL_TailGeometry.capacity slot-32*count)%8=0 :=
 ⟨(NKL_TailGeometry.counted_prefix slot count s bound).1,
  (NKL_TailGeometry.counted_prefix slot count s bound).2,
  (NKL_TailGeometry.suffix slot count s bound).1,
  (NKL_TailGeometry.suffix slot count s bound).2⟩

#print axioms scaled_value
#print axioms checked_scale
#print axioms fits
end NKV_TailArithmetic
