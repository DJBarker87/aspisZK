-- PCWK_ (phase P5b): fresh (frozen 4bb3b3f, overflow ON) = gate for M31.mul in AspisV8R19.{Guarded,Complex,Quartic}FieldSlice,
-- and the gate-only helper r23_product_u32_bounded (QuarticFieldSlice). Lemma blocks PCVB_M31 / PCVB_R23 are verbatim from
-- evidence/prov-p3x-20261110/PRVEq_AspisR72Sampler_Funs_A2.lean (P3b lemmas). All theorems run at the default maxHeartbeats 200000.
import Aeneas
import AspisV8R19.QuarticFieldSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

/- PCVB generic arithmetic lemmas (phase P3b, M31.mul): see PCVB_m31_lemmas.lean -/
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

theorem fast_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val ≤ 4611686014132420609) :
    fastBody P x ⦃ r => r.val = Fv x.val ⦄ := by
  unfold fastBody
  step*
  all_goals (
    subst_vars
    simp only [hmask P hP, hshr, hcast32, hcast64, hP, ge_iff_le, UScalar.le_equiv, h64d, Fv] at *
    first | omega | (split_ifs <;> omega))

theorem e31 : (2:Nat)^31 = 2147483648 := by norm_num
theorem e32 : (2:Nat)^32 = 4294967296 := by norm_num

theorem mA (x : Nat) (hx : x ≤ 4611686014132420609) : x % 2147483648 + x / 2147483648 ≤ 4294967293 := by omega

theorem mB (A : Nat) (hA : A ≤ 4294967293) :
    (A % 2147483648 + A / 2147483648) % 4294967296 = A % 2147483648 + A / 2147483648 := by omega

theorem core (A : Nat) (hA : A ≤ 4294967293) :
    (if 2147483647 ≤ A % 2147483648 + A / 2147483648 then A % 2147483648 + A / 2147483648 - 2147483647 else A % 2147483648 + A / 2147483648)
    = (if 2147483647 ≤ A then A - 2147483647 else A) := by
  have h1 : A % 2147483648 < 2147483648 := Nat.mod_lt _ (by decide)
  have h2 : A / 2147483648 ≤ 1 := by omega
  have h3 := Nat.mod_add_div A 2147483648
  split_ifs <;> omega

theorem arith {x x1 x2 i1 i2 i4 i5 r : Nat} (hx : x ≤ 4611686014132420609) (h1 : i1 = x % 2^31) (h2 : i2 = x / 2^31)
    (hx1 : x1 = i1 + i2) (h4 : i4 = x1 % 2^31) (h5 : i5 = x1 / 2^31) (hx2 : x2 = i4 + i5)
    (hr : r = if 2147483647 ≤ x2 % 2^32 then x2 % 2^32 - 2147483647 else x2 % 2^32) : r = Fv x := by
  unfold Fv
  subst h1 h2 hx1 h4 h5 hx2
  simp only [e31, e32] at *
  rw [mB _ (mA x hx)] at hr
  exact hr.trans (core _ (mA x hx))

theorem red_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val ≤ 4611686014132420609) :
    redBody P x ⦃ r => r.val = Fv x.val ⦄ := by
  unfold redBody
  step*
  all_goals (
    subst_vars
    simp only [hmask P hP, hshr, hcast32, hP, ge_iff_le, UScalar.le_equiv, h64d] at *)
  · omega
  · omega
  · exact arith hx i1_post1 i2_post1 x1_post i4_post1 i5_post1 x2_post (by rw [if_pos r_post2]; exact r_post1)
  · exact arith hx i1_post1 i2_post1 x1_post i4_post1 i5_post1 x2_post (by rw [if_neg ‹_›])

theorem fast_eq (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) (hx : x.val ≤ 4611686014132420609) :
    fastBody P x = redBody P x := by
  obtain ⟨r1, h1, v1⟩ := WP.spec_imp_exists (fast_spec P hP x hx)
  obtain ⟨r2, h2, v2⟩ := WP.spec_imp_exists (red_spec P hP x hx)
  rw [h1, h2]
  congr 1
  exact UScalar.eq_imp _ _ (v1.trans v2.symm)


theorem fast_chain (P : Std.U32) (hP : P.val = 2147483647) (R : Std.U64 → Result Std.U32)
    (hR : ∀ x, R x = redBody P x) (a b : Std.U32) (ha : a < P) (hb : b < P) :
    (do let i ← lift (UScalar.cast .U64 a)
        let i1 ← lift (UScalar.cast .U64 b)
        let i2 ← i * i1
        let i3 ← R i2
        ok i3) =
    (do let i ← lift (UScalar.cast .U64 a)
        let i1 ← lift (UScalar.cast .U64 b)
        let x ← i * i1
        fastBody P x) := by
  have ha' : a.val < 2147483647 := by have := (UScalar.lt_equiv a P).mp ha; omega
  have hb' : b.val < 2147483647 := by have := (UScalar.lt_equiv b P).mp hb; omega
  have hprod : a.val * b.val ≤ 4611686014132420609 := by
    have := Nat.mul_le_mul (show a.val ≤ 2147483646 by omega) (show b.val ≤ 2147483646 by omega)
    omega
  have hia : (UScalar.cast .U64 a).val = a.val := U32.cast_U64_val_eq a
  have hib : (UScalar.cast .U64 b).val = b.val := U32.cast_U64_val_eq b
  have hm : (UScalar.cast .U64 a : Std.U64) * (UScalar.cast .U64 b : Std.U64) ⦃ z => z.val = a.val * b.val ⦄ := by
    have hmax : (UScalar.cast .U64 a).val * (UScalar.cast .U64 b).val ≤ U64.max := by
      rw [hia, hib, h64d]; omega
    have := U64.mul_spec hmax
    simpa [hia, hib] using this
  obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists hm
  simp only [lift, bind_tc_ok, hz]
  have hfe := fast_eq P hP z (by omega)
  rw [hR z, ← hfe]
  cases fastBody P z <;> rfl

#print axioms fast_chain
theorem redarith {x x1 x2 i1 i2 i4 i5 r : Nat} (hx : x < 18446744073709551616) (h1 : i1 = x % 2^31) (h2 : i2 = x / 2^31)
    (hx1 : x1 = i1 + i2) (h4 : i4 = x1 % 2^31) (h5 : i5 = x1 / 2^31) (hx2 : x2 = i4 + i5)
    (hr : r = if 2147483647 ≤ x2 % 2^32 then x2 % 2^32 - 2147483647 else x2 % 2^32) : r = x % 2147483647 := by
  subst h1 h2 hx1 h4 h5 hx2
  simp only [e31, e32] at *
  have e0 := Nat.mod_add_div x 2147483648
  have hb : x / 2147483648 < 8589934592 := by omega
  have ha : x % 2147483648 < 2147483648 := Nat.mod_lt _ (by omega)
  generalize x % 2147483648 = a at *
  generalize x / 2147483648 = b at *
  have e1 := Nat.mod_add_div (a + b) 2147483648
  have hc : (a + b) % 2147483648 < 2147483648 := Nat.mod_lt _ (by omega)
  have hd : (a + b) / 2147483648 < 8 := by omega
  generalize (a + b) % 2147483648 = c at *
  generalize (a + b) / 2147483648 = d at *
  have hlt : c + d < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt] at hr
  split_ifs at hr <;> omega

set_option maxHeartbeats 200000 in
theorem red_val_spec (P : Std.U32) (hP : P.val = 2147483647) (x : Std.U64) :
    redBody P x ⦃ r => r.val = x.val % 2147483647 ⦄ := by
  have hx : x.val < 18446744073709551616 := by scalar_tac
  unfold redBody
  step*
  all_goals (
    subst_vars
    simp only [hmask P hP, hshr, hcast32, hcast64, hP, ge_iff_le, UScalar.le_equiv, h64d] at *)
  · omega
  · omega
  · exact redarith hx i1_post1 i2_post1 x1_post i4_post1 i5_post1 x2_post (by rw [if_pos r_post2]; exact r_post1)
  · exact redarith hx i1_post1 i2_post1 x1_post i4_post1 i5_post1 x2_post (by rw [if_neg ‹_›])

end PCVB_M31

namespace PCVB_R23
def r23 (left : Std.U64) (right : Std.U64) : Result Std.U64 := do
  let i ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
  if left <= i
  then
    let i1 ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
    if right <= i1
    then
      let i2 ← lift (UScalar.cast .U32 left)
      let i3 ← lift (core.convert.num.FromU64U32.from i2)
      let i4 ← lift (UScalar.cast .U32 right)
      let i5 ← lift (core.convert.num.FromU64U32.from i4)
      i3 * i5
    else left * right
  else left * right

theorem hmaxA : (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq]; rfl

theorem hcastF (l : Std.U64) (h : l.val ≤ 4294967295) :
    core.convert.num.FromU64U32.from (UScalar.cast .U32 l) = l := by
  apply UScalar.eq_imp
  rw [core.convert.num.FromU64U32.from_val_eq, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
  exact Nat.mod_eq_of_lt (by omega)

theorem r23_eq (l r : Std.U64) : r23 l r = l * r := by
  unfold r23
  simp only [lift, bind_tc_ok]
  split_ifs with h1 h2
  · have a1 := (UScalar.le_equiv _ _).mp h1
    have a2 := (UScalar.le_equiv _ _).mp h2
    rw [hmaxA] at a1 a2
    rw [hcastF l a1, hcastF r a2]
  · rfl
  · rfl

#print axioms r23_eq
end PCVB_R23

namespace AspisR64Field
namespace PRVFresh_AspisV8R19_GuardedFieldSlice

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

end PRVFresh_AspisV8R19_GuardedFieldSlice
end AspisR64Field

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.GuardedFieldSlice.field.P : @AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.P = @AspisR64Field.field.P := by
  delta AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.P AspisR64Field.field.P; try rfl; done
#print axioms PRVEq.AspisV8R19.GuardedFieldSlice.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.GuardedFieldSlice.field.reduce_u64 : @AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.reduce_u64 = @AspisR64Field.field.reduce_u64 := by
  delta AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.reduce_u64 AspisR64Field.field.reduce_u64; try simp only [PRVEq.AspisV8R19.GuardedFieldSlice.field.P]; try rfl; done
#print axioms PRVEq.AspisV8R19.GuardedFieldSlice.field.reduce_u64

-- The gate guard is total on U32 x U32 (the non-fast branches are the frozen reduce_u64 (a*b)); the fast branch is
-- equal to it for a, b < P by PCVB_M31.fast_chain.
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.GuardedFieldSlice.field.M31.mul : @AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.M31.mul = @AspisR64Field.field.M31.mul := by
  funext self rhs
  have hr : @AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.reduce_u64 = @AspisR64Field.field.reduce_u64 := PRVEq.AspisV8R19.GuardedFieldSlice.field.reduce_u64
  have hP : (AspisR64Field.field.P : Std.U32).val = 2147483647 := by
    unfold AspisR64Field.field.P; rfl
  unfold AspisR64Field.PRVFresh_AspisV8R19_GuardedFieldSlice.field.M31.mul AspisR64Field.field.M31.mul
  rw [hr]
  by_cases h1 : self < AspisR64Field.field.P
  · by_cases h2 : rhs < AspisR64Field.field.P
    · rw [if_pos h1, if_pos h2]
      exact PCVB_M31.fast_chain AspisR64Field.field.P hP AspisR64Field.field.reduce_u64 (fun x => rfl) self rhs h1 h2
    · rw [if_pos h1, if_neg h2]
      try rfl
  · rw [if_neg h1]
    try rfl
#print axioms PRVEq.AspisV8R19.GuardedFieldSlice.field.M31.mul

namespace AspisR65Field
namespace PRVFresh_AspisV8R19_ComplexFieldSlice

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

end PRVFresh_AspisV8R19_ComplexFieldSlice
end AspisR65Field

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.ComplexFieldSlice.field.P : @AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.P = @AspisR65Field.field.P := by
  delta AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.P AspisR65Field.field.P; try rfl; done
#print axioms PRVEq.AspisV8R19.ComplexFieldSlice.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.ComplexFieldSlice.field.reduce_u64 : @AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.reduce_u64 = @AspisR65Field.field.reduce_u64 := by
  delta AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.reduce_u64 AspisR65Field.field.reduce_u64; try simp only [PRVEq.AspisV8R19.ComplexFieldSlice.field.P]; try rfl; done
#print axioms PRVEq.AspisV8R19.ComplexFieldSlice.field.reduce_u64

-- The gate guard is total on U32 x U32 (the non-fast branches are the frozen reduce_u64 (a*b)); the fast branch is
-- equal to it for a, b < P by PCVB_M31.fast_chain.
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul : @AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.M31.mul = @AspisR65Field.field.M31.mul := by
  funext self rhs
  have hr : @AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.reduce_u64 = @AspisR65Field.field.reduce_u64 := PRVEq.AspisV8R19.ComplexFieldSlice.field.reduce_u64
  have hP : (AspisR65Field.field.P : Std.U32).val = 2147483647 := by
    unfold AspisR65Field.field.P; rfl
  unfold AspisR65Field.PRVFresh_AspisV8R19_ComplexFieldSlice.field.M31.mul AspisR65Field.field.M31.mul
  rw [hr]
  by_cases h1 : self < AspisR65Field.field.P
  · by_cases h2 : rhs < AspisR65Field.field.P
    · rw [if_pos h1, if_pos h2]
      exact PCVB_M31.fast_chain AspisR65Field.field.P hP AspisR65Field.field.reduce_u64 (fun x => rfl) self rhs h1 h2
    · rw [if_pos h1, if_neg h2]
      try rfl
  · rw [if_neg h1]
    try rfl
#print axioms PRVEq.AspisV8R19.ComplexFieldSlice.field.M31.mul

namespace AspisR66Field
namespace PRVFresh_AspisV8R19_QuarticFieldSlice

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::reduce_u64]:
    Source: 'crates/aspis-core/src/field.rs', lines 31:0-44:1 -/
def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

/-- [aspis_core::field::{aspis_core::field::M31}::mul]:
    Source: 'crates/aspis-core/src/field.rs', lines 133:4-137:5
    Visibility: public -/
def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

end PRVFresh_AspisV8R19_QuarticFieldSlice
end AspisR66Field

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.QuarticFieldSlice.field.P : @AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.P = @AspisR66Field.field.P := by
  delta AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.P AspisR66Field.field.P; try rfl; done
#print axioms PRVEq.AspisV8R19.QuarticFieldSlice.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.QuarticFieldSlice.field.reduce_u64 : @AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.reduce_u64 = @AspisR66Field.field.reduce_u64 := by
  delta AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.reduce_u64 AspisR66Field.field.reduce_u64; try simp only [PRVEq.AspisV8R19.QuarticFieldSlice.field.P]; try rfl; done
#print axioms PRVEq.AspisV8R19.QuarticFieldSlice.field.reduce_u64

-- The gate guard is total on U32 x U32 (the non-fast branches are the frozen reduce_u64 (a*b)); the fast branch is
-- equal to it for a, b < P by PCVB_M31.fast_chain.
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul : @AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.M31.mul = @AspisR66Field.field.M31.mul := by
  funext self rhs
  have hr : @AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.reduce_u64 = @AspisR66Field.field.reduce_u64 := PRVEq.AspisV8R19.QuarticFieldSlice.field.reduce_u64
  have hP : (AspisR66Field.field.P : Std.U32).val = 2147483647 := by
    unfold AspisR66Field.field.P; rfl
  unfold AspisR66Field.PRVFresh_AspisV8R19_QuarticFieldSlice.field.M31.mul AspisR66Field.field.M31.mul
  rw [hr]
  by_cases h1 : self < AspisR66Field.field.P
  · by_cases h2 : rhs < AspisR66Field.field.P
    · rw [if_pos h1, if_pos h2]
      exact PCVB_M31.fast_chain AspisR66Field.field.P hP AspisR66Field.field.reduce_u64 (fun x => rfl) self rhs h1 h2
    · rw [if_pos h1, if_neg h2]
      try rfl
  · rw [if_neg h1]
    try rfl
#print axioms PRVEq.AspisV8R19.QuarticFieldSlice.field.M31.mul

-- P5b: AspisV8R19.QuarticFieldSlice field.r23_product_u32_bounded (source r23_width.rs) has no frozen counterpart at
-- 4bb3b3f; it is a gate-only helper of the gate CM31.mul / CM31.square. Both guards only select an equal-valued u32
-- round trip, so it equals the checked u64 product on ALL inputs (total, no domain).
set_option maxHeartbeats 200000 in
theorem PRVEq.AspisV8R19.QuarticFieldSlice.field.r23_gate : ∀ l r, AspisR66Field.field.r23_product_u32_bounded l r = l * r := fun l r => PCVB_R23.r23_eq l r
#print axioms PRVEq.AspisV8R19.QuarticFieldSlice.field.r23_gate
