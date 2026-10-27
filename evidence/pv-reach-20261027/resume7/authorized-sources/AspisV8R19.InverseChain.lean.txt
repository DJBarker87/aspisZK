import AspisV8R17.RawReducer
import AspisV8R15.ExactTowerBase
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! The literal M31 inverse addition chain, proved symbolically. Word
multiplication uses the retained raw reducer, not a fresh inversion oracle.
This does not assert extraction of the Rust range-loop or panic machinery. -/
set_option autoImplicit false
namespace AspisV8R19.InverseChain
open AspisV8R15.ExactTowerBase

def squares {A : Type*} (mul : A → A → A) : Nat → A → A
  | 0, x => x
  | n+1, x => squares mul n (mul x x)

def chain {A : Type*} (mul : A → A → A) (x : A) : A :=
  let t2 := mul (mul x x) x
  let t4 := mul (squares mul 2 t2) t2
  let t8 := mul (squares mul 4 t4) t4
  let t16 := mul (squares mul 8 t8) t8
  let t24 := mul (squares mul 8 t16) t8
  let t28 := mul (squares mul 4 t24) t4
  let t29 := mul (mul t28 t28) x
  let t30 := mul t29 t29
  mul (mul t30 t30) x

theorem map_squares {A B : Type*} (f : A → B) (ma : A → A → A) (mb : B → B → B)
    (hm : ∀ a b, f (ma a b) = mb (f a) (f b)) (n : Nat) (x : A) :
    f (squares ma n x) = squares mb n (f x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [squares,ih,hm]

theorem map_chain {A B : Type*} (f : A → B) (ma : A → A → A) (mb : B → B → B)
    (hm : ∀ a b, f (ma a b) = mb (f a) (f b)) (x : A) :
    f (chain ma x) = chain mb (f x) := by
  simp only [chain,hm,map_squares f ma mb hm]

theorem squares_pow {A : Type*} [Monoid A] (n : Nat) (x : A) :
    squares (fun a b : A => a*b) n x = x^(2^n) := by
  induction n generalizing x with
  | zero => simp [squares]
  | succ n ih =>
      rw [squares,ih,← pow_two,← pow_mul]
      congr 1
      simp [pow_succ,Nat.mul_comm]

theorem chain_pow {A : Type*} [Monoid A] (x : A) :
    chain (fun a b : A => a*b) x = x^2147483645 := by
  have h3 : x*x*x = x^3 := by simp [pow_succ]
  simp only [chain,h3,squares_pow,← pow_mul,← pow_add,← pow_succ]
  norm_num

abbrev Word := Fin P
def wordMul (a b : Word) : Word :=
  ⟨AspisV8R17.RawReducer.rawM31Mul a.val b.val,
    AspisV8R17.RawReducer.rawM31Mul_canonical a.isLt b.isLt⟩
def decode (a : Word) : M31Exact := a.val
def wordChain (a : Word) : Word := chain wordMul a

theorem decode_wordMul (a b : Word) : decode (wordMul a b) = decode a * decode b :=
  AspisV8R17.RawReducer.rawM31Mul_residue a.isLt b.isLt

theorem decode_wordChain (a : Word) : decode (wordChain a) = decode a ^ (P-2) := by
  unfold wordChain
  rw [map_chain decode wordMul (fun a b : M31Exact => a*b) decode_wordMul,chain_pow]
  rfl

theorem decode_zero (a : Word) : decode a = 0 ↔ a.val = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [decode,ZMod.val_natCast_of_lt a.isLt] using hv
  · intro h; simp [decode,h]

theorem wordChain_inverse (a : Word) (ha : a.val ≠ 0) :
    decode (wordChain a) = (decode a)⁻¹ := by
  have hne : decode a ≠ 0 := fun h => ha ((decode_zero a).mp h)
  apply (mul_right_inj' hne).mp
  rw [mul_inv_cancel₀ hne,decode_wordChain,mul_comm]
  have hp := ZMod.pow_card_sub_one_eq_one hne
  rw [show P-1 = (P-2)+1 by decide,pow_succ] at hp
  exact hp

def guarded (a : Word) : Except Unit Word :=
  if a.val = 0 then .error () else .ok (wordChain a)

theorem zero_rejected (a : Word) (ha : a.val = 0) : guarded a = .error () := by
  simp [guarded,ha]

theorem nonzero_success (a : Word) (ha : a.val ≠ 0) :
    guarded a = .ok (wordChain a) ∧ decode (wordChain a) = (decode a)⁻¹ :=
  ⟨by simp [guarded,ha],wordChain_inverse a ha⟩

#print axioms map_squares
#print axioms map_chain
#print axioms squares_pow
#print axioms chain_pow
#print axioms decode_wordMul
#print axioms decode_wordChain
#print axioms decode_zero
#print axioms wordChain_inverse
#print axioms zero_rejected
#print axioms nonzero_success
end AspisV8R19.InverseChain
