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

theorem chain_exponent (x : U32) :
    decode (inverseWord x)=decode x^(P-2) := by
  simp only [inverseWord,word_mul,square_decode,←pow_two,←pow_mul,←pow_add]
  rfl

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
#print axioms chain_exponent
#print axioms inverse_decode
end AspisR1.S7JoinInverseBackend
