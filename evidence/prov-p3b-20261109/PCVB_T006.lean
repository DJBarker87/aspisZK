import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace PCVB_M31
theorem m1 (s : Nat) (hs : s ≤ 4294967294) : s % 2147483648 + s / 2147483648 < 4294967296 := by omega
theorem m2 (x : Nat) (hx : x < 4611686018427387904) : x / 2147483648 < 2147483648 := by omega
theorem m3 (x : Nat) : x % 2147483648 < 2147483648 := by omega
theorem m4 (x : Nat) (hx : x < 4611686018427387904) : x % 2147483648 + x / 2147483648 ≤ 4294967294 := by omega
theorem m5 (s : Nat) (hs : s ≤ 4294967294) : (s % 2147483648 + s / 2147483648) % 4294967296 = s % 2147483648 + s / 2147483648 := by omega
theorem m6 (s : Nat) (hs : s ≤ 4294967294) : (s % 2147483648 + s / 2147483648) % 4294967296 = s % 2147483648 + s / 2147483648 :=
  Nat.mod_eq_of_lt (m1 s hs)
theorem m7 (s : Nat) (hs : s ≤ 4294967294) (u v : Nat) (hu : u = s % 2147483648) (hv : v = s / 2147483648) : v ≤ 1 := by omega
theorem m8 (u v s : Nat) (h : s = 2147483648 * v + u) (hu : u < 2147483648) (hs : s ≤ 4294967294) : v ≤ 1 := by omega
theorem m9 (x : Nat) (hx : x < 4611686018427387904) : x % 2147483648 + x / 2147483648 ≤ 4294967294 := by
  have := Nat.mod_add_div x 2147483648
  have h1 := Nat.mod_lt x (show 2147483648 > 0 by decide)
  have h2 : x / 2147483648 < 2147483648 := Nat.div_lt_of_lt_mul (by omega)
  omega
end PCVB_M31
