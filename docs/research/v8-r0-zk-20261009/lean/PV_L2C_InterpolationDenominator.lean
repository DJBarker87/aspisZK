import PV_L2C_InterpolationNodes
set_option autoImplicit false
namespace PV_L2C_InterpolationDenominator
open PV_L2C_M31
local instance : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩

def raw (i : Nat) : word := BitVec.ofNat 32 i

theorem raw_canonical (i : Nat) (hi : i < 28) : canonical (raw i) := by
  change i%2^32 < 2147483647
  rw [Nat.mod_eq_of_lt (by omega)]
  omega
#print axioms raw_canonical

theorem raw_decoded (i : Nat) (hi : i < 28) : decode (raw i) = PV_L2C_InterpolationNodes.node i := by
  unfold decode raw PV_L2C_InterpolationNodes.node
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
#print axioms raw_decoded

def run (i : Nat) : Nat → word
  | 0 => 1
  | n+1 => if n=i then run i n else
      PV_L2C_NativeMultiply.mul (run i n) (sub (raw i) (raw n))

theorem canonical_result (i n : Nat) : canonical (run i n) := by
  induction n with
  | zero => change 1 < 2147483647;omega
  | succ n ih =>
    rw [run]
    split
    · exact ih
    · exact PV_L2C_NativeMultiply.canonical_result _ _
#print axioms canonical_result

theorem decoded (i n : Nat) (hi : i < 28) (hn : n ≤ 28) :
    decode (run i n) = PV_L2C_InterpolationNodes.denominator i n := by
  induction n with
  | zero => simp [run,PV_L2C_InterpolationNodes.denominator,decode]
  | succ n ih =>
    have hsmall : n < 28 := by omega
    rw [run,PV_L2C_InterpolationNodes.denominator,Finset.prod_range_succ]
    by_cases he : n=i
    · rw [if_pos he,if_pos he]
      simpa only [mul_one,PV_L2C_InterpolationNodes.denominator] using ih (by omega)
    · rw [if_neg he,if_neg he,PV_L2C_NativeMultiply.decoded,
        sub_decode _ _ (raw_canonical i hi) (raw_canonical n hsmall),
        raw_decoded i hi,raw_decoded n hsmall]
      rw [ih (by omega)]
      rfl
#print axioms decoded

theorem nonzero (i n : Nat) (hi : i < 28) (hn : n ≤ 28) : decode (run i n) ≠ 0 := by
  rw [decoded i n hi hn]
  exact PV_L2C_InterpolationNodes.nonzero i n hi hn
#print axioms nonzero

theorem inverse (i : Nat) (hi : i < 28) :
    PV_L2C_NativeInverse.run (run i 28) = .ok (PV_L2C_NativeInverse.chain (run i 28)) ∧
    canonical (PV_L2C_NativeInverse.chain (run i 28)) ∧
    decode (PV_L2C_NativeInverse.chain (run i 28)) = (decode (run i 28))⁻¹ :=
  PV_L2C_InverseField.complete _ (canonical_result i 28) (nonzero i 28 hi (by omega))
#print axioms inverse
end PV_L2C_InterpolationDenominator
