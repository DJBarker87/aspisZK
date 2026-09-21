import AspisV8R17.UnsignedCoreSlice

/-! Checked execution of the lazy cross operand. Source-marked aliases and
conversion are authenticated; the extracted CM31 caller composition is pending. -/
namespace Aeneas.Std
-- SOURCE Core.lean
abbrev  U32   := UScalar .U32
-- END SOURCE
-- SOURCE Core.lean
abbrev  U64   := UScalar .U64
-- END SOURCE
namespace core.convert.num
-- SOURCE CoreConvertNum.lean
def FromU64U32.from (x : U32) : U64 := ⟨ x.bv.setWidth _ ⟩
-- END SOURCE
end core.convert.num
-- SOURCE Ops/Add.lean
instance {ty} : HAdd (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hAdd x y := UScalar.add x y
-- END SOURCE
-- SOURCE Ops/Mul.lean
instance {ty} : HMul (UScalar ty) (UScalar ty) (Result (UScalar ty)) where
  hMul x y := UScalar.mul x y
-- END SOURCE
end Aeneas.Std

namespace V7Tag73CurrentHelpersOpaque
open Aeneas
-- GENERATED Types.lean
@[reducible, rust_type "aspis_core::field::M31"]
def aspis_core.field.M31 := Std.U32
-- END GENERATED
-- GENERATED Types.lean
@[rust_type "aspis_core::field::CM31"]
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.UnsignedCM31Cross
open Aeneas.Std UnsignedCoreSlice

theorem widen_value (x : U32) : (core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

def crossOperand (a b c d : U32) : Result U64 := do
  let left ← UScalar.add (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b)
  let right ← UScalar.add (core.convert.num.FromU64U32.from c)
    (core.convert.num.FromU64U32.from d)
  UScalar.mul left right

theorem crossOperand_success (a b c d : U32)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647) :
    ∃ product : U64, crossOperand a b c d = .ok product ∧
      product.val = (a.val+b.val)*(c.val+d.val) := by
  have hab : a.val+b.val < 2^32 := by omega
  have hcd : c.val+d.val < 2^32 := by omega
  have hleft : (core.convert.num.FromU64U32.from a).val +
      (core.convert.num.FromU64U32.from b).val < 2^64 := by
    rw [widen_value, widen_value]
    omega
  have hright : (core.convert.num.FromU64U32.from c).val +
      (core.convert.num.FromU64U32.from d).val < 2^64 := by
    rw [widen_value, widen_value]
    omega
  obtain ⟨left, hl, hvl⟩ := add_success _ _ hleft
  obtain ⟨right, hr, hvr⟩ := add_success _ _ hright
  rw [widen_value, widen_value] at hvl hvr
  have hprod : left.val*right.val < 2^64 := by
    rw [hvl, hvr]
    have h := Nat.mul_lt_mul_of_lt_of_lt hab hcd
    exact h
  obtain ⟨product, hp, hvp⟩ := mul_success left right hprod
  refine ⟨product, ?_, ?_⟩
  · simp only [crossOperand, hl, hr, bind_tc_ok, hp]
  · simpa only [hvl, hvr] using hvp

open V7Tag73CurrentHelpersOpaque

/-- The contiguous cross-operand subexpression of the pinned generated caller.
The preceding m0/m1 computations and following reducer are NOT included. -/
def generatedCrossFragment (self rhs : aspis_core.field.CM31) : Result U64 := do
-- GENERATED FunsChunk04.lean
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
-- END GENERATED
  .ok i10

private theorem bind_return_word (r : Result U64) :
    (do let x ← r; .ok x) = r := by
  cases r <;> rfl

theorem generatedCrossFragment_eq (self rhs : aspis_core.field.CM31) :
    generatedCrossFragment self rhs = crossOperand self.a self.b rhs.a rhs.b := by
  simp only [generatedCrossFragment, crossOperand, Aeneas.Std.lift,
    bind_tc_ok, bind_return_word]
  rfl

theorem generatedCrossFragment_success (self rhs : aspis_core.field.CM31)
    (ha : self.a.val < 2147483647) (hb : self.b.val < 2147483647)
    (hc : rhs.a.val < 2147483647) (hd : rhs.b.val < 2147483647) :
    ∃ product : U64, generatedCrossFragment self rhs = .ok product ∧
      product.val = (self.a.val+self.b.val)*(rhs.a.val+rhs.b.val) := by
  rw [generatedCrossFragment_eq]
  exact crossOperand_success _ _ _ _ ha hb hc hd

#print axioms widen_value
#print axioms crossOperand_success
#print axioms generatedCrossFragment_eq
#print axioms generatedCrossFragment_success
end AspisV8R17.UnsignedCM31Cross
