import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
namespace R17TableBasePowerProbe
abbrev P : Nat := 2147483647
structure C where
  re : Nat
  im : Nat
  deriving DecidableEq

def addM (a b : Nat) : Nat := (a % P + b % P) % P
def subM (a b : Nat) : Nat := (a % P + P - b % P) % P
def mulM (a b : Nat) : Nat := (a % P * (b % P)) % P
def cmul (x y : C) : C := ⟨subM (x.re*y.re) (x.im*y.im), addM (x.re*y.im) (x.im*y.re)⟩
def cone : C := ⟨1,0⟩
def gen : C := ⟨2,1268011823⟩
def fastPow (x : C) : Nat → C
| 0 => cone
| n+1 =>
  let y := fastPow x ((n+1)/2)
  if (n+1)%2 == 0 then cmul y y else cmul (cmul y y) x
termination_by n => n
decreasing_by omega

theorem tableA_zero_matches_generator :
    fastPow gen 1024 = ⟨1022251061, 788094511⟩ := by
  norm_num [fastPow, cmul, cone, gen, addM, subM, mulM]

#print axioms tableA_zero_matches_generator
end R17TableBasePowerProbe
