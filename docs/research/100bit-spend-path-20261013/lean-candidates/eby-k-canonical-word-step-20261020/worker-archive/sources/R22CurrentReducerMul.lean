import CheckedWrappingScalarAgreement
import ExtractedCurrentReducer

/-! R22: for every stored U64 reducer input and every pair of stored U32
multiplication inputs, the actual checked source is total and agrees with
its wrapping-primitive expression. Reuses the existing symbolic totality and
modular arithmetic proof, without assuming a whole-verifier range invariant. -/
set_option autoImplicit false
namespace AspisR1.R22CurrentReducerMul
open Aeneas Aeneas.Std Result
open CheckedWrappingScalarAgreement ExtractedCurrentReducerOps
open ExtractedCurrentReducer

def high (x : U64) : U64 := ⟨x.bv.ushiftRight 31⟩
def wrappingFold (x : U64) : U64 :=
  UScalar.wrapping_add (UScalar.and x mask64) (high x)

theorem fold_agrees (x : U64) : foldExecution x = ok (wrappingFold x) := by
  obtain ⟨y,hy,_⟩ := foldExecution_success x
  have hs : UScalar.shiftRight x 31 = ok (high x) := by
    simp only [UScalar.shiftRight,high]; rfl
  have ha : UScalar.add (UScalar.and x mask64) (high x) = ok y := by
    simpa only [foldExecution,hs,bind_tc_ok] using hy
  have hw := (add_success_agrees _ _ _ ha).1
  simpa only [wrappingFold,hw] using hy

def wrappingReduce (x : U64) : U32 :=
  let n := UScalar.cast .U32 (wrappingFold (wrappingFold x))
  if AspisV8R17.RawReducer.P ≤ n.val then UScalar.wrapping_sub n mask32 else n

theorem reduce_agrees (x : U64) : reduceExecution x = ok (wrappingReduce x) := by
  rw [reduceExecution,fold_agrees]
  simp only [bind_tc_ok,fold_agrees]
  let n := UScalar.cast .U32 (wrappingFold (wrappingFold x))
  by_cases h : AspisV8R17.RawReducer.P ≤ n.val
  · obtain ⟨z,hz,_⟩ := sub_success n mask32 (by simpa only [mask32_value] using h)
    have hw := (sub_success_agrees _ _ _ hz).1
    change (if AspisV8R17.RawReducer.P ≤ n.val then UScalar.sub n mask32 else ok n) =
      ok (if AspisV8R17.RawReducer.P ≤ n.val then UScalar.wrapping_sub n mask32 else n)
    simp only [h,if_pos,hz,hw]
  · change (if AspisV8R17.RawReducer.P ≤ n.val then UScalar.sub n mask32 else ok n) =
      ok (if AspisV8R17.RawReducer.P ≤ n.val then UScalar.wrapping_sub n mask32 else n)
    simp only [h,if_false]

theorem current_reducer_agrees (x : U64) :
    AspisR1Qm31ArithmeticProbe.field.reduce_u64 x = ok (wrappingReduce x) := by
  rw [current_reducer_eq,reduce_agrees]

def wrappingMul (x y : AspisR1Qm31ArithmeticProbe.field.M31) :
    AspisR1Qm31ArithmeticProbe.field.M31 :=
  wrappingReduce (UScalar.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))

theorem current_mul_agrees (x y : AspisR1Qm31ArithmeticProbe.field.M31) :
    AspisR1Qm31ArithmeticProbe.field.M31.mul x y = ok (wrappingMul x y) := by
  have hproduct : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < 2^64 := by
    rw [cast_widen_value,cast_widen_value]
    have h := Nat.mul_lt_mul_of_lt_of_lt x.bv.isLt y.bv.isLt
    exact h
  obtain ⟨p,hp,_⟩ := mul_success _ _ hproduct
  have hw := (mul_success_agrees _ _ _ hp).1
  simp only [AspisR1Qm31ArithmeticProbe.field.M31.mul,lift,bind_tc_ok]
  change (do let p ← UScalar.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
             let r ← AspisR1Qm31ArithmeticProbe.field.reduce_u64 p
             ok r) = ok (wrappingMul x y)
  simp only [hp,bind_tc_ok,current_reducer_agrees,wrappingMul,hw]

theorem wrapping_reduce_mod (x : U64) :
    (wrappingReduce x).val = x.val % AspisV8R17.RawReducer.P ∧
    (wrappingReduce x).val < AspisV8R17.RawReducer.P := by
  obtain ⟨z,hz,hm,hc⟩ := current_reduce_mod x
  rw [current_reducer_agrees] at hz
  exact Result.ok.inj hz ▸ ⟨hm,hc⟩

theorem wrapping_mul_mod (x y : AspisR1Qm31ArithmeticProbe.field.M31) :
    (wrappingMul x y).val = (x.val*y.val) % AspisV8R17.RawReducer.P ∧
    (wrappingMul x y).val < AspisV8R17.RawReducer.P := by
  obtain ⟨z,hz,hm,hc⟩ := current_mul_mod x y
  rw [current_mul_agrees] at hz
  exact Result.ok.inj hz ▸ ⟨hm,hc⟩

#print axioms fold_agrees
#print axioms reduce_agrees
#print axioms current_reducer_agrees
#print axioms current_mul_agrees
#print axioms wrapping_reduce_mod
#print axioms wrapping_mul_mod
end AspisR1.R22CurrentReducerMul
