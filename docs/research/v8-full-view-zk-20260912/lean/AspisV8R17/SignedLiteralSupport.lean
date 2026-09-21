import AspisV8R17.SignedShiftSlice
import Lean.Elab.Tactic.Omega

/-! Signed literal constructors from the pinned runtime. bound_suffices has
the runtime statement with a direct proof. SOURCE blocks retain source bytes;
PROOF ADAPTED retains the executable constructor with a core bounds proof. -/
namespace Aeneas.Std

-- SOURCE Core.lean
def I8.rMin   : Int := -128
def I8.rMax   : Int := 127
def I16.rMin  : Int := -32768
def I16.rMax  : Int := 32767
def I32.rMin  : Int := -2147483648
def I32.rMax  : Int := 2147483647
def I64.rMin  : Int := -9223372036854775808
def I64.rMax  : Int := 9223372036854775807
def I128.rMin : Int := -170141183460469231731687303715884105728
def I128.rMax : Int := 170141183460469231731687303715884105727
def Isize.rMin : Int := -2^(System.Platform.numBits - 1)
def Isize.rMax : Int := 2^(System.Platform.numBits - 1)-1
-- END SOURCE

-- SOURCE Core.lean
def IScalar.rMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMin
  | .I8    => I8.rMin
  | .I16   => I16.rMin
  | .I32   => I32.rMin
  | .I64   => I64.rMin
  | .I128  => I128.rMin
-- END SOURCE

-- SOURCE Core.lean
def IScalar.rMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMax
  | .I8    => I8.rMax
  | .I16   => I16.rMax
  | .I32   => I32.rMax
  | .I64   => I64.rMax
  | .I128  => I128.rMax
-- END SOURCE

-- SOURCE Core.lean
def IScalar.cMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMin .I32
  | _ => IScalar.rMin ty
-- END SOURCE

-- SOURCE Core.lean
def IScalar.cMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMax .I32
  | _ => IScalar.rMax ty
-- END SOURCE

theorem IScalar.bound_suffices (ty : IScalarTy) (x : Int) :
    IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty →
    -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1) := by
  intro h
  cases ty <;> simp only [IScalar.cMin, IScalar.cMax, IScalar.rMin,
    IScalar.rMax, IScalarTy.numBits, I8.rMin, I8.rMax, I16.rMin,
    I16.rMax, I32.rMin, I32.rMax, I64.rMin, I64.rMax,
    I128.rMin, I128.rMax] at *
  all_goals first | omega |
    (rcases System.Platform.numBits_eq with hbits | hbits <;> rw [hbits] <;> omega)

-- PROOF ADAPTED Core.lean
def IScalar.ofIntCore {ty : IScalarTy} (x : Int) (_ : -2^(ty.numBits-1) ≤ x ∧ x < 2^(ty.numBits - 1)) : IScalar ty :=
  -- TODO: we should leave `x` unchanged if it is positive, so that expressions like `(1#isize).val` can reduce to `1`
  let x' := (x % 2^ty.numBits).toNat
  have h : x' < 2^ty.numBits := by
    apply (Int.toNat_lt' (Nat.two_pow_pos ty.numBits)).mpr
    exact Int.emod_lt_of_pos x (Int.pow_pos (by decide))
  { bv := ⟨ x', h ⟩ }
-- END PROOF ADAPTED

-- SOURCE Core.lean
@[reducible] def IScalar.ofInt {ty : IScalarTy} (x : Int)
  (hInBounds : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty := by decide) : IScalar ty :=
  IScalar.ofIntCore x (IScalar.bound_suffices ty x hInBounds)
-- END SOURCE

-- SOURCE Core.lean
abbrev I32.ofInt   := @IScalar.ofInt .I32
-- END SOURCE
end Aeneas.Std

namespace AspisV8R17.SignedLiteralSupport
open Aeneas.Std

theorem one_value : (I32.ofInt 1).val = 1 := by decide
theorem thirty_value : (I32.ofInt 30).val = 30 := by decide
theorem one_toNat : (I32.ofInt 1).toNat = 1 := by decide
theorem thirty_toNat : (I32.ofInt 30).toNat = 30 := by decide
theorem literal_proof_irrelevant (n : Int)
    (h h' : IScalar.cMin .I32 ≤ n ∧ n ≤ IScalar.cMax .I32) :
    I32.ofInt n h = I32.ofInt n h' := rfl

#print axioms IScalar.bound_suffices
#print axioms one_value
#print axioms thirty_value
#print axioms one_toNat
#print axioms thirty_toNat
#print axioms literal_proof_irrelevant
end AspisV8R17.SignedLiteralSupport
