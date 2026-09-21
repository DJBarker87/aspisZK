import AspisV8R17.UnsignedReducerExecution

/-! Literal-constructor and comparison semantics for the generated reducer.
The #u32 macro itself is not imported here: these prove the meaning of its
U32.ofNat expansion for every admissible proof of the literal bound. -/
namespace Aeneas.Std

-- SOURCE Core.lean
def U8.rMax   : Nat := 255
def U16.rMax  : Nat := 65535
def U32.rMax  : Nat := 4294967295
def U64.rMax  : Nat := 18446744073709551615
def U128.rMax : Nat := 340282366920938463463374607431768211455
def Usize.rMax : Nat := 2^System.Platform.numBits-1
-- END SOURCE

-- SOURCE Core.lean
def UScalar.rMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => Usize.rMax
  | .U8    => U8.rMax
  | .U16   => U16.rMax
  | .U32   => U32.rMax
  | .U64   => U64.rMax
  | .U128  => U128.rMax
-- END SOURCE

-- SOURCE Core.lean
def UScalar.cMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => UScalar.rMax .U32
  | _ => UScalar.rMax ty
-- END SOURCE

private theorem cMax_lt_width (ty : UScalarTy) : UScalar.cMax ty < 2^ty.numBits := by
  cases ty <;> simp only [UScalar.cMax, UScalar.rMax, UScalarTy.numBits,
    U8.rMax, U16.rMax, U32.rMax, U64.rMax, U128.rMax]
  all_goals first | decide |
    (rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide)

/-- Same statement as the runtime helper, using a small direct proof. -/
theorem UScalar.bound_suffices (ty : UScalarTy) (x : Nat) :
    x ≤ UScalar.cMax ty -> x < 2^ty.numBits := by
  intro h
  exact Nat.lt_of_le_of_lt h (cMax_lt_width ty)

-- SOURCE Core.lean
@[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore x (UScalar.bound_suffices ty x hInBounds)
-- END SOURCE

-- SOURCE Core.lean
abbrev U32.ofNat   := @UScalar.ofNat .U32
-- END SOURCE

-- SOURCE Core.lean
instance {ty} : LE (UScalar ty) where le a b := LE.le a.val b.val
-- END SOURCE

/- Same runtime instance statement; explicit construction avoids relying on
the larger runtime's transitive DecidableRel instance-search infrastructure. -/
instance UScalarDecidableLE (ty: UScalarTy) : DecidableRel (· ≤ · : UScalar ty -> UScalar ty -> Prop) := by
  intro x y
  exact Nat.decLe x.val y.val
end Aeneas.Std

namespace AspisV8R17.UnsignedLiteralSupport
open Aeneas.Std UnsignedReducerExecution

theorem literal_value (n : Nat) (h : n ≤ UScalar.cMax .U32) :
    (U32.ofNat n h).val = n := rfl

theorem literal_proof_irrelevant (n : Nat) (h h' : n ≤ UScalar.cMax .U32) :
    U32.ofNat n h = U32.ofNat n h' := rfl

theorem literal_P_eq_mask (h : 2147483647 ≤ UScalar.cMax .U32) :
    U32.ofNat 2147483647 h = mask32 := rfl

theorem literal_shift_value (h : 31 ≤ UScalar.cMax .U32) :
    (U32.ofNat 31 h).val = 31 := rfl

theorem comparison_value {ty : UScalarTy} (x y : UScalar ty) :
    (x ≥ y) ↔ y.val ≤ x.val := Iff.rfl

theorem reducer_branch (x : U32) (h : 2147483647 ≤ UScalar.cMax .U32)
    (yes no : Result U32) :
    (if x ≥ U32.ofNat 2147483647 h then yes else no) =
      (if RawReducer.P ≤ x.val then yes else no) := rfl

#print axioms literal_value
#print axioms literal_proof_irrelevant
#print axioms literal_P_eq_mask
#print axioms literal_shift_value
#print axioms comparison_value
#print axioms reducer_branch
end AspisV8R17.UnsignedLiteralSupport
