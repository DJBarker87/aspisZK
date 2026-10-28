import PV_L2C_NativeMultiply
import PV_L2C_InverseChain
set_option autoImplicit false
namespace PV_L2C_NativeInverse
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_NativeMultiply

def squareN : word → Nat → word
  | x,0 => x
  | x,n+1 => squareN (mul x x) n

theorem square_decoded (x : word) (n : Nat) : decode (squareN x n) = decode x^(2^n) := by
  induction n generalizing x with
  | zero => simp [squareN]
  | succ n ih =>
    rw [squareN,ih,decoded]
    rw [← pow_two,← pow_mul]
    congr 1
    omega
#print axioms square_decoded

def chain (x : word) : word :=
  let t2 := mul (mul x x) x
  let t4 := mul (squareN t2 2) t2
  let t8 := mul (squareN t4 4) t4
  let t16 := mul (squareN t8 8) t8
  let t24 := mul (squareN t16 8) t8
  let t28 := mul (squareN t24 4) t4
  let t29 := mul (mul t28 t28) x
  let t30 := mul t29 t29
  mul (mul t30 t30) x

theorem canonical_chain (x : word) : canonical (chain x) := canonical_result _ _
#print axioms canonical_chain

theorem decoded_chain (x : word) : decode (chain x) = decode x^2147483645 := by
  change decode (chain x) = _
  have he : decode (chain x) = PV_L2C_InverseChain.chain (decode x) := by
    simp only [chain,PV_L2C_InverseChain.chain,decoded,square_decoded]
  rw [he,PV_L2C_InverseChain.exponent]
#print axioms decoded_chain

/-- The native assert on raw zero is retained as panic; it is not replaced
by a total inverse at zero. -/
def run (x : word) : Result word := if x = 0 then .fail .panic else ok (chain x)

theorem zero : run 0 = .fail .panic := by rw [run,if_pos rfl]
#print axioms zero

theorem success (x : word) (hx : canonical x) (hz : decode x ≠ 0) :
    run x = ok (chain x) ∧ canonical (chain x) ∧ decode (chain x) = decode x^2147483645 := by
  have hraw : x ≠ 0 := by intro he;subst x;exact hz (by rfl)
  exact ⟨by rw [run,if_neg hraw],canonical_chain x,decoded_chain x⟩
#print axioms success
end PV_L2C_NativeInverse
