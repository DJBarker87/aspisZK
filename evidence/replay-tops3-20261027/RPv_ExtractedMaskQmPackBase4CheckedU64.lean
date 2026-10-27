import ExtractedMaskReducerOps
import ExtractedMaskReducer
import RPv_Qm31PackBase4Slice
import RPv_ExtractedMaskQmPackBase4Arithmetic

/-! Checked U64 call helpers used by the exact current packer sequence. -/
set_option autoImplicit false
namespace AspisR1.ExtractedMaskQmPackBase4CheckedU64

open Aeneas.Std Result
open AspisR1.ExtractedMaskReducerOps
open AspisR1.ExtractedMaskQmPackBase4Arithmetic

private def u64Nat (n : Nat) (hn : n < 2^64) : U64 :=
  UScalar.ofNatCore n hn

@[simp] private theorem u64Nat_val (n : Nat) (hn : n < 2^64) :
    (u64Nat n hn).val = n := rfl

theorem add_nat (a b : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (hs : a + b < 2^64) :
    ∃ z : U64, UScalar.add (u64Nat a ha) (u64Nat b hb) = .ok z ∧
      z.val = a + b := by
  obtain ⟨z, hz, hv⟩ := add_success (u64Nat a ha) (u64Nat b hb) (by
    simpa using hs)
  exact ⟨z, by simpa [u64Nat] using hz, by simpa [u64Nat] using hv⟩

theorem sub_nat (a b : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (hs : b ≤ a) :
    ∃ z : U64, UScalar.sub (u64Nat a ha) (u64Nat b hb) = .ok z ∧
      z.val = a - b := by
  obtain ⟨z, hz, hv⟩ := sub_success (u64Nat a ha) (u64Nat b hb) (by
    simpa using hs)
  exact ⟨z, by simpa [u64Nat] using hz, by simpa [u64Nat] using hv⟩

theorem mul_nat (a b : Nat) (ha : a < 2^64) (hb : b < 2^64)
    (hs : a * b < 2^64) :
    ∃ z : U64, UScalar.mul (u64Nat a ha) (u64Nat b hb) = .ok z ∧
      z.val = a * b := by
  obtain ⟨z, hz, hv⟩ := mul_success (u64Nat a ha) (u64Nat b hb) (by
    simpa using hs)
  exact ⟨z, by simpa [u64Nat] using hz, by simpa [u64Nat] using hv⟩

/-- The generated closure conversion returns the U64 widening of one source
M31 limb. -/
def limbToU64 (x : AspisR1SelectedMaskProbe.field.M31) : U64 :=
  UScalar.cast .U64 x

def packLimbCall (x : AspisR1SelectedMaskProbe.field.M31) : Result U64 :=
  AspisR1SelectedMaskProbe.field.qm31_pack_base4.closure.Insts.CoreOpsFunctionFnTupleM31U64.call
    () x

theorem packLimbCall_eq_cast (x : AspisR1SelectedMaskProbe.field.M31) :
    packLimbCall x = .ok (limbToU64 x) := by
  rfl

theorem limbToU64_val (x : AspisR1SelectedMaskProbe.field.M31) :
    (limbToU64 x).val = x.val := by
  exact AspisR1.ExtractedMaskReducer.cast_widen_value x

#print axioms add_nat
#print axioms sub_nat
#print axioms mul_nat
#print axioms packLimbCall_eq_cast
#print axioms limbToU64_val
end AspisR1.ExtractedMaskQmPackBase4CheckedU64
