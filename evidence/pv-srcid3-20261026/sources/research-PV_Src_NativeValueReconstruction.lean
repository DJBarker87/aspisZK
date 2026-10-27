import R1Z.PV_Src_LowBits
import R1Z.PV_Src_NativeValueBits

/-! The actual returned value-bit array reconstructs every admitted source
value. Its bound is the shipped value range, not an unannounced restriction. -/
set_option autoImplicit false
namespace R1Z.PV_Src_NativeValueReconstruction
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort.pool_v1

theorem reconstruct (value : U32) (bound : value.val < 2^30) :
    ∃ out, pair_trace.value_bits value = ok out ∧
      (∑ n ∈ Finset.range 30, 2^n * (out.val[n]!).val) = value.val := by
  obtain ⟨out,ho,hc⟩ := PV_Src_NativeValueBits.cells value
  refine ⟨out,ho,?_⟩
  calc
    _ = ∑ n ∈ Finset.range 30, 2^n * (value.val / 2^n % 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hc n (Finset.mem_range.mp hn)]
    _ = value.val % 2^30 := PV_Src_LowBits.sum value.val 30
    _ = value.val := Nat.mod_eq_of_lt bound

#print axioms reconstruct
end R1Z.PV_Src_NativeValueReconstruction
