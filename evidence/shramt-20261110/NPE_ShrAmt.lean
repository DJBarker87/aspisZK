import Aeneas
open Aeneas Aeneas.Std Result

/-! NPE_ 2026-11-10: ShrAmt bridge (PCQH inputs/PCQH_shr_prelude.lean) against Rust's shift semantics.
Rust reference, "Arithmetic and Logical Binary Operators" / "Overflow": with overflow checks off, `x >> y` and
`x << y` use only the low log2(BITS) bits of the right operand (two's complement for a signed operand), i.e. the
amount is `y mod BITS` (Euclidean, so a negative `y` gives the same low bits). We state that meaning here as
`rustShr`/`rustShl` with the amount taken as an integer and reduced by `Int.emod` modulo the Usize width. -/

namespace NPE

def W : Nat := UScalarTy.numBits .Usize

/-- Rust wrapping (`overflow-checks = off`) `x >> y` on usize, for a right operand of any integer type given by its
mathematical value `y : Int` (a usize or u32 amount is its Nat value, an i32 amount its signed value). -/
def rustShr (x : Std.Usize) (y : Int) : Std.Usize := ⟨x.bv.ushiftRight (Int.toNat (y % (W : Int)))⟩
def rustShl (x : Std.Usize) (y : Int) : Std.Usize := ⟨x.bv.shiftLeft (Int.toNat (y % (W : Int)))⟩

theorem amt_i32 (y : Std.I32) :
    (IScalar.hcast .U32 y).val % UScalarTy.numBits .Usize = Int.toNat (y.val % (W : Int)) := by
  rw [IScalar.hcast_val_eq]
  unfold W
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalarTy.numBits, IScalarTy.numBits, h, Nat.reducePow, Int.reducePow, Nat.cast_ofNat] <;> omega

theorem amt_usize (y : Std.Usize) :
    (UScalar.cast .U32 y).val % UScalarTy.numBits .Usize = Int.toNat ((y.val : Int) % (W : Int)) := by
  rw [UScalar.cast_val_eq]
  unfold W
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalarTy.numBits, h, Nat.reducePow, Int.reducePow, Nat.cast_ofNat] <;> omega

/-- OFF configuration, i32 amount (the NFN fibre_point site `index >> 9`): the bridge equals Rust for all amounts. -/
theorem bridge_shr_i32 (x : Std.Usize) (y : Std.I32) :
    Aeneas.Std.Usize.wrapping_shr x (IScalar.hcast .U32 y) = rustShr x y.val := by
  simp only [Aeneas.Std.Usize.wrapping_shr, UScalar.wrapping_shr, rustShr]
  rw [amt_i32]

theorem bridge_shl_i32 (x : Std.Usize) (y : Std.I32) :
    Aeneas.Std.Usize.wrapping_shl x (IScalar.hcast .U32 y) = rustShl x y.val := by
  simp only [Aeneas.Std.Usize.wrapping_shl, UScalar.wrapping_shl, rustShl]
  rw [amt_i32]

/-- OFF configuration, usize amount (the RPz7 row_loop.body sites): the bridge equals Rust for all amounts. -/
theorem bridge_shr_usize (x y : Std.Usize) :
    Aeneas.Std.Usize.wrapping_shr x (UScalar.cast .U32 y) = rustShr x (y.val : Int) := by
  simp only [Aeneas.Std.Usize.wrapping_shr, UScalar.wrapping_shr, rustShr]
  rw [amt_usize]

theorem bridge_shl_usize (x y : Std.Usize) :
    Aeneas.Std.Usize.wrapping_shl x (UScalar.cast .U32 y) = rustShl x (y.val : Int) := by
  simp only [Aeneas.Std.Usize.wrapping_shl, UScalar.wrapping_shl, rustShl]
  rw [amt_usize]

/-- Checked configuration, i32 amount: rustc emits `assert((y as u32) < BITS)`. The `as u32`-then-U32 test fails
exactly when that assertion fails (here written against the library's checked shift on a U32 amount). -/
theorem checked_i32_via_u32 (x : Std.Usize) (y : Std.I32) :
    UScalar.shiftRight x (IScalar.hcast .U32 y).val =
      (if (IScalar.hcast .U32 y).val < UScalarTy.numBits .Usize then ok ⟨x.bv.ushiftRight (IScalar.hcast .U32 y).val⟩
       else fail Error.integerOverflow) := by
  rfl

/-- The library's direct checked shift on an I32 amount fails iff y < 0 or y >= W, which is the same set as
(y as u32) >= W, the rustc assertion. -/
theorem checked_i32_direct_iff (y : Std.I32) :
    ((y.val ≥ 0 ∧ y.val.toNat < UScalarTy.numBits .Usize) ↔ (IScalar.hcast .U32 y).val < UScalarTy.numBits .Usize) := by
  rw [IScalar.hcast_val_eq]
  have hb := y.hmin; have hb2 := y.hmax
  rcases System.Platform.numBits_eq with h | h <;>
    simp only [UScalarTy.numBits, IScalarTy.numBits, h, Nat.reducePow, Int.reducePow] at * <;> omega

end NPE

-- concrete instances
example : IScalar.hcast .U32 (9#i32) = 9#u32 := by rfl
example : (IScalar.hcast .U32 (⟨-1⟩ : Std.I32)).val = 4294967295 := by decide
example : (IScalar.hcast .U32 (⟨-55⟩ : Std.I32)).val = 4294967241 := by decide
example : (IScalar.hcast .U32 (⟨(-2147483648 : BitVec 32)⟩ : Std.I32)).val = 2147483648 := by decide

#print axioms NPE.amt_i32
#print axioms NPE.amt_usize
#print axioms NPE.bridge_shr_i32
#print axioms NPE.bridge_shl_i32
#print axioms NPE.bridge_shr_usize
#print axioms NPE.bridge_shl_usize
#print axioms NPE.checked_i32_via_u32
#print axioms NPE.checked_i32_direct_iff
