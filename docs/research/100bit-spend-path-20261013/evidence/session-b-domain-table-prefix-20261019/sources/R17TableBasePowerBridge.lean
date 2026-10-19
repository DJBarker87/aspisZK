import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace R17TableBasePowerBridge
abbrev P : Nat := 2147483647
structure NatC where
  re : Nat
  im : Nat
  deriving DecidableEq
@[ext]
structure ZC where
  re : ZMod P
  im : ZMod P

def addM (a b : Nat) : Nat := (a % P + b % P) % P
def subM (a b : Nat) : Nat := (a % P + P - b % P) % P
def natMul (x y : NatC) : NatC := ⟨subM (x.re*y.re) (x.im*y.im), addM (x.re*y.im) (x.im*y.re)⟩
def zMul (x y : ZC) : ZC := ⟨x.re*y.re-x.im*y.im, x.re*y.im+x.im*y.re⟩
def decode (x : NatC) : ZC := ⟨x.re, x.im⟩
def oneN : NatC := ⟨1,0⟩
def oneZ : ZC := ⟨1,0⟩
def natPow (x : NatC) : Nat → NatC
| 0 => oneN
| n+1 =>
  let y := natPow x ((n+1)/2)
  if (n+1)%2 == 0 then natMul y y else natMul (natMul y y) x
termination_by n => n
decreasing_by omega
def zPow (x : ZC) : Nat → ZC
| 0 => oneZ
| n+1 =>
  let y := zPow x ((n+1)/2)
  if (n+1)%2 == 0 then zMul y y else zMul (zMul y y) x
termination_by n => n
decreasing_by omega

theorem subM_decode (a b : Nat) :
    ((subM a b : Nat) : ZMod P) = (a : ZMod P) - (b : ZMod P) := by
  unfold subM
  have hb : b % P < P := Nat.mod_lt _ (by norm_num [P])
  have hle : b % P ≤ a % P + P := by omega
  calc
    (((a % P + P - b % P) % P : Nat) : ZMod P) =
        ((a % P + P - b % P : Nat) : ZMod P) := ZMod.natCast_mod _ _
    _ = (a % P : ZMod P) + (P : ZMod P) - (b % P : ZMod P) := by
      rw [Nat.cast_sub hle, Nat.cast_add]
    _ = (a : ZMod P) - (b : ZMod P) := by
      rw [ZMod.natCast_mod, ZMod.natCast_self, add_zero, ZMod.natCast_mod]

theorem addM_decode (a b : Nat) :
    ((addM a b : Nat) : ZMod P) = (a : ZMod P) + (b : ZMod P) := by
  unfold addM
  calc
    (((a % P + b % P) % P : Nat) : ZMod P) =
        ((a % P + b % P : Nat) : ZMod P) := ZMod.natCast_mod _ _
    _ = (a % P : ZMod P) + (b % P : ZMod P) := by rw [Nat.cast_add]
    _ = (a : ZMod P) + (b : ZMod P) := by
      rw [ZMod.natCast_mod, ZMod.natCast_mod]


theorem natMul_decode (x y : NatC) : decode (natMul x y) = zMul (decode x) (decode y) := by
  ext <;> simp [natMul, zMul, decode, subM_decode, addM_decode]

theorem natPow_decode_zPow (x : NatC) (n : Nat) : decode (natPow x n) = zPow (decode x) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [natPow, zPow, oneN, oneZ, decode]
    | succ k =>
      have hm : (k+1)/2 < k+1 := by omega
      have him := ih ((k+1)/2) hm
      simp only [natPow, zPow]
      by_cases hparity : (k + 1) % 2 == 0
      · simp only [if_pos hparity]
        simp only [natMul_decode, him]
      · simp only [if_neg hparity]
        simp only [natMul_decode, him]

#print axioms subM_decode
#print axioms addM_decode
#print axioms natMul_decode
#print axioms natPow_decode_zPow
end R17TableBasePowerBridge
