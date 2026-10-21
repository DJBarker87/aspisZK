import S7JoinBasisMachine
import Mathlib.FieldTheory.Finite.Basic

/-! Field semantics of the frozen fixed addition chain. This is an explicit
word-level reference port; binding the opaque emitted M31.inv remains a P6
source/extraction obligation. No inverse law is assumed. -/
set_option autoImplicit false
namespace AspisR1.S7JoinInverseBackend
open Aeneas.Std
open AspisCircleGroupOrder
open S7Kani2PrefixLoop (wordMul)
open S7JoinBasisMachine (decode word_mul)

def squareN : U32 → Nat → U32
  | x,0 => x
  | x,n+1 => squareN (wordMul x x) n

def inverseWord (x : U32) : U32 :=
  let t2 := wordMul (wordMul x x) x
  let t4 := wordMul (squareN t2 2) t2
  let t8 := wordMul (squareN t4 4) t4
  let t16 := wordMul (squareN t8 8) t8
  let t24 := wordMul (squareN t16 8) t8
  let t28 := wordMul (squareN t24 4) t4
  let t29 := wordMul (wordMul t28 t28) x
  let t30 := wordMul t29 t29
  wordMul (wordMul t30 t30) x

theorem square_decode (x : U32) (n : Nat) :
    decode (squareN x n)=decode x^(2^n) := by
  induction n generalizing x with
  | zero => simp only [squareN,pow_zero,pow_one]
  | succ n ih =>
      rw [squareN,ih,word_mul,←pow_two,←pow_mul,pow_succ,Nat.mul_comm]

theorem power_step (x a b : U32) (i j n : Nat)
    (ha : decode a=decode x^i) (hb : decode b=decode x^j) :
    decode (wordMul (squareN a n) b)=decode x^(i*2^n+j) := by
  rw [word_mul,square_decode,ha,hb,←pow_mul,←pow_add]

theorem chain_exponent (x : U32) :
    decode (inverseWord x)=decode x^(P-2) := by
  let t2 := wordMul (wordMul x x) x
  have h2 : decode t2=decode x^3 := by
    dsimp only [t2]
    rw [word_mul,word_mul]
    ring
  let t4 := wordMul (squareN t2 2) t2
  have h4 : decode t4=decode x^15 := power_step x t2 t2 3 3 2 h2 h2
  let t8 := wordMul (squareN t4 4) t4
  have h8 : decode t8=decode x^255 := power_step x t4 t4 15 15 4 h4 h4
  let t16 := wordMul (squareN t8 8) t8
  have h16 : decode t16=decode x^65535 := power_step x t8 t8 255 255 8 h8 h8
  let t24 := wordMul (squareN t16 8) t8
  have h24 : decode t24=decode x^16777215 := power_step x t16 t8 65535 255 8 h16 h8
  let t28 := wordMul (squareN t24 4) t4
  have h28 : decode t28=decode x^268435455 := power_step x t24 t4 16777215 15 4 h24 h4
  have hx : decode x=decode x^1 := (pow_one _).symm
  have h29 : decode (wordMul (squareN t28 1) x)=decode x^536870911 :=
    power_step x t28 x 268435455 1 1 h28 hx
  have h31 := power_step x (wordMul (squareN t28 1) x) x 536870911 1 2 h29 hx
  exact h31

theorem inverse_decode (x : U32) : decode (inverseWord x)=(decode x)⁻¹ := by
  rw [chain_exponent]
  by_cases hz : decode x=0
  · rw [hz,zero_pow (by decide : P-2≠0),inv_zero]
  · apply (mul_left_cancel₀ hz)
    rw [mul_inv_cancel₀ hz,←pow_succ']
    have he : P-2+1=P-1 := by rfl
    rw [he]
    exact ZMod.pow_card_sub_one_eq_one hz

#print axioms square_decode
#print axioms power_step
#print axioms chain_exponent
#print axioms inverse_decode
end AspisR1.S7JoinInverseBackend
