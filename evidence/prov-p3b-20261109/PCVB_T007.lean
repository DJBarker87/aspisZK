import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace PCVB_M31
theorem c1 (A : Nat) (hA : A ≤ 4294967294) :
    (if 2147483647 ≤ A % 2147483648 + A / 2147483648 then A % 2147483648 + A / 2147483648 - 2147483647 else A % 2147483648 + A / 2147483648)
    = (if 2147483647 ≤ A then A - 2147483647 else A) := by
  split_ifs <;> omega
theorem c2 (A : Nat) (hA : A ≤ 4294967294) :
    (if 2147483647 ≤ A % 2147483648 + A / 2147483648 then A % 2147483648 + A / 2147483648 - 2147483647 else A % 2147483648 + A / 2147483648)
    = (if 2147483647 ≤ A then A - 2147483647 else A) := by
  by_cases h : 2147483647 ≤ A
  · rw [if_pos h]
    by_cases h2 : 2147483647 ≤ A % 2147483648 + A / 2147483648
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega
  · rw [if_neg h]
    have : A % 2147483648 + A / 2147483648 = A := by omega
    rw [this, if_neg h]
theorem c3 (A : Nat) (hA : A ≤ 4294967294) :
    (if 2147483647 ≤ A % 2147483648 + A / 2147483648 then A % 2147483648 + A / 2147483648 - 2147483647 else A % 2147483648 + A / 2147483648)
    = (if 2147483647 ≤ A then A - 2147483647 else A) := by
  have h1 : A % 2147483648 < 2147483648 := Nat.mod_lt _ (by decide)
  have h2 : A / 2147483648 ≤ 1 := by omega
  have h3 := Nat.mod_add_div A 2147483648
  split_ifs <;> omega
end PCVB_M31
