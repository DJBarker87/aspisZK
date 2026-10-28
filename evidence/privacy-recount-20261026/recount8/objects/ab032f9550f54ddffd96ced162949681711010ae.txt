import R1Z.ProverCommitRelease47
import R1Z.ProverCommitNativeOps47
import ExtractedCurrentReducer
import Mathlib.FieldTheory.Finite.Basic
/-! Focused fixed-inverse port. The retained algebra is copied without its
unrelated geometry imports. The current native fixed-chain caller and square
iteration are bound separately by P6 callee-trace Kani gates. -/
set_option autoImplicit false
namespace R1Z.ProverCommitInverse48
open Aeneas Aeneas.Std Result AspisCircleGroupOrder

def decode (x : U32) : ZMod P := x.val
def wordMul (x y : U32) : U32 :=
  UScalar.ofNatCore ((x.val*y.val)%P) (by
    have hm := Nat.mod_lt (x.val*y.val) (show 0<P by decide)
    have hp : P<2^32 := by decide
    change (x.val*y.val)%P<2^32
    exact Nat.lt_trans hm hp)

theorem multiply_word (x y : U32) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y=ok (wordMul x y) := by
  obtain ⟨z,hz,hvalue,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
  have he : z=wordMul x y := UScalar.eq_of_val_eq hvalue
  simpa only [he] using hz

theorem word_mul (x y : U32) : decode (wordMul x y)=decode x*decode y := by
  change (((x.val*y.val)%P : Nat) : ZMod P)=(x.val : ZMod P)*(y.val : ZMod P)
  rw [ZMod.natCast_mod,Nat.cast_mul]

theorem release_multiply (x y : U32) :
    AspisR1ProducerRelease47.field.M31.mul x y=ok (wordMul x y) := by
  have checked : AspisR1ProducerChecked47.field.M31.mul x y=ok (wordMul x y) := by
    rw [ProverCommitPrimitive47.mMul,multiply_word]
  exact ProverCommitRelease47.mMul x y (wordMul x y) checked

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

def square_owned : U32 → Nat → Result U32
 | x,0 => ok x
 | x,n+1 => do
     let y ← AspisR1ProducerRelease47.field.M31.mul x x
     square_owned y n

def inverse_owned (x : U32) : Result U32 := do
  massert (x≠0#u32)
  let a ← AspisR1ProducerRelease47.field.M31.mul x x
  let t2 ← AspisR1ProducerRelease47.field.M31.mul a x
  let a ← square_owned t2 2
  let t4 ← AspisR1ProducerRelease47.field.M31.mul a t2
  let a ← square_owned t4 4
  let t8 ← AspisR1ProducerRelease47.field.M31.mul a t4
  let a ← square_owned t8 8
  let t16 ← AspisR1ProducerRelease47.field.M31.mul a t8
  let a ← square_owned t16 8
  let t24 ← AspisR1ProducerRelease47.field.M31.mul a t8
  let a ← square_owned t24 4
  let t28 ← AspisR1ProducerRelease47.field.M31.mul a t4
  let a ← AspisR1ProducerRelease47.field.M31.mul t28 t28
  let t29 ← AspisR1ProducerRelease47.field.M31.mul a x
  let t30 ← AspisR1ProducerRelease47.field.M31.mul t29 t29
  let a ← AspisR1ProducerRelease47.field.M31.mul t30 t30
  AspisR1ProducerRelease47.field.M31.mul a x

theorem square_result (x : U32) (n : Nat) :
    square_owned x n=ok (squareN x n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [square_owned,release_multiply,bind_tc_ok,ih,squareN]

/-- Complete Result equality, including assertion failure on raw zero. -/
theorem inverse_result (x : U32) : inverse_owned x = (do
    massert (x≠0#u32)
    ok (inverseWord x)) := by
  simp only [inverse_owned,square_result,release_multiply,bind_tc_ok,inverseWord]

/-- Semantic inversion for every input accepted by the raw-word assertion. -/
theorem inverse_exact (x : U32) (hx : x≠0#u32) :
    ∃ y, inverse_owned x=ok y ∧ decode y=(decode x)⁻¹ := by
  refine ⟨inverseWord x,?_,inverse_decode x⟩
  rw [inverse_result]
  simp [hx]

theorem inverse_canonical (x : U32) : (inverseWord x).val<AspisCircleGroupOrder.P := by
  unfold inverseWord wordMul
  exact Nat.mod_lt _ (by decide)

#print axioms multiply_word
#print axioms word_mul
#print axioms release_multiply
#print axioms square_decode
#print axioms power_step
#print axioms chain_exponent
#print axioms inverse_decode
#print axioms square_result
#print axioms inverse_result
#print axioms inverse_exact
#print axioms inverse_canonical
end R1Z.ProverCommitInverse48
