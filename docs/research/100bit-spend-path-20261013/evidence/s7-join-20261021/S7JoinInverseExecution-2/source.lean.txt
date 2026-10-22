import S7JoinInverseBackend

/-! Checked-call port of field.rs's feature-off fixed inverse chain.
The source zero assertion is retained. This does not identify an opaque
extracted declaration with its body or supply an operational translation. -/
set_option autoImplicit false
namespace AspisR1.S7JoinInverseExecution
open Aeneas Aeneas.Std Result
open S7JoinInverseBackend S7JoinBasisMachine
open S7Kani2PrefixLoop (wordMul multiply_word)

def square_owned : U32 → Nat → Result U32
 | x,0 => ok x
 | x,n+1 => do
     let y ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
     square_owned y n

def inverse_owned (x : U32) : Result U32 := do
  massert (x≠0#u32)
  let a ← AspisR1Qm31ArithmeticProbe.field.M31.mul x x
  let t2 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a x
  let a ← square_owned t2 2
  let t4 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a t2
  let a ← square_owned t4 4
  let t8 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a t4
  let a ← square_owned t8 8
  let t16 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a t8
  let a ← square_owned t16 8
  let t24 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a t8
  let a ← square_owned t24 4
  let t28 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a t4
  let a ← AspisR1Qm31ArithmeticProbe.field.M31.mul t28 t28
  let t29 ← AspisR1Qm31ArithmeticProbe.field.M31.mul a x
  let t30 ← AspisR1Qm31ArithmeticProbe.field.M31.mul t29 t29
  let a ← AspisR1Qm31ArithmeticProbe.field.M31.mul t30 t30
  AspisR1Qm31ArithmeticProbe.field.M31.mul a x

theorem square_result (x : U32) (n : Nat) :
    square_owned x n=ok (squareN x n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [square_owned,multiply_word,bind_tc_ok,ih,squareN]

/-- Complete Result equality, including assertion failure on raw zero. -/
theorem inverse_result (x : U32) : inverse_owned x = (do
    massert (x≠0#u32)
    ok (inverseWord x)) := by
  simp only [inverse_owned,square_result,multiply_word,bind_tc_ok,inverseWord]

/-- Semantic inversion for every input accepted by the raw-word assertion. -/
theorem inverse_exact (x : U32) (hx : x≠0#u32) :
    ∃ y, inverse_owned x=ok y ∧ decode y=(decode x)⁻¹ := by
  refine ⟨inverseWord x,?_,inverse_decode x⟩
  rw [inverse_result]
  simp [hx]

theorem inverse_canonical (x : U32) : (inverseWord x).val<AspisCircleGroupOrder.P := by
  unfold inverseWord wordMul
  exact Nat.mod_lt _ (by decide)

#print axioms inverse_canonical
#print axioms square_result
#print axioms inverse_result
#print axioms inverse_exact
end AspisR1.S7JoinInverseExecution
