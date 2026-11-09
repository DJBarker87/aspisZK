import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace PCVB_M31

def redBody (P : Std.U32) (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= P
  then x3 - P
  else ok x3

def fastBody (P : Std.U32) (x : Std.U64) : Result Std.U32 := do
  let i2 ← lift (UScalar.cast .U64 P)
  let i3 ← lift (x &&& i2)
  let i4 ← x >>> 31#i32
  let s ← i3 + i4
  let i5 ← lift (UScalar.cast .U64 P)
  if s >= i5
  then
    let i6 ← lift (UScalar.cast .U64 P)
    let i7 ← s - i6
    let i8 ← lift (UScalar.cast .U32 i7)
    ok i8
  else let i6 ← lift (UScalar.cast .U32 s)
       ok i6

def Fv (n : Nat) : Nat :=
  if 2147483647 ≤ n % 2^31 + n / 2^31 then n % 2^31 + n / 2^31 - 2147483647 else n % 2^31 + n / 2^31

theorem h64d : (U64.max : Nat) = 18446744073709551615 := by scalar_tac

theorem hmask (P : Std.U32) (hP : P.val = 2147483647) (y : Std.U64) :
    (y &&& UScalar.cast .U64 P).val = y.val % 2^31 := by
  rw [UScalar.val_and, U32.cast_U64_val_eq, hP, show (2147483647:Nat) = 2^31 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

theorem hshr (y : Std.U64) (n : Nat) : y.val >>> n = y.val / 2^n := Nat.shiftRight_eq_div_pow _ _

theorem hcast32 (z : Std.U64) : (UScalar.cast .U32 z).val = z.val % 2^32 := by
  rw [UScalar.cast_val_eq]; rfl

theorem hcast64 (P : Std.U32) : (UScalar.cast .U64 P).val = P.val := U32.cast_U64_val_eq P

theorem fast_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val < 2^62) :
    fastBody P x ⦃ r => r.val = Fv x.val ⦄ := by
  unfold fastBody
  step*
  all_goals (
    subst_vars
    simp only [hmask P hP, hshr, hcast32, hcast64, hP, ge_iff_le, UScalar.le_equiv, h64d, Fv] at *
    first | omega | (split_ifs <;> omega))

theorem red_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val < 2^62) :
    redBody P x ⦃ r => r.val = Fv x.val ⦄ := by
  unfold redBody
  step*
  all_goals (
    subst_vars
    simp only [hmask P hP, hshr, hcast32, hcast64, hP, ge_iff_le, UScalar.le_equiv, h64d, Fv] at *
    trace_state
    first | omega | (split_ifs <;> omega))

theorem fast_eq (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val < 2^62) :
    fastBody P x = redBody P x := by
  obtain ⟨r1, h1, v1⟩ := WP.spec_imp_exists (fast_spec P hP x hx)
  obtain ⟨r2, h2, v2⟩ := WP.spec_imp_exists (red_spec P hP x hx)
  rw [h1, h2]
  congr 1
  exact UScalar.eq_imp _ _ (v1.trans v2.symm)

#print axioms fast_eq
end PCVB_M31
