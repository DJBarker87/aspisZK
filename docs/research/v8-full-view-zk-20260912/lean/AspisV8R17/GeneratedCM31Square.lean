import AspisV8R17.GeneratedM31Add

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::square"]
def aspis_core.field.CM31.square
  (self : aspis_core.field.CM31) : Result aspis_core.field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← i4 * i9
  let m ← aspis_core.field.M31.reduce_u64 i10
  let m1 ← aspis_core.field.M31.mul self.a self.b
  let m2 ← aspis_core.field.M31.double m1
  ok { a := m, b := m2 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedCM31Square
open Aeneas.Std V7Tag73CurrentHelpersOpaque RawReducer
open UnsignedCoreSlice UnsignedReducerOps UnsignedCM31Cross
open GeneratedM31Mul GeneratedM31Sub GeneratedM31Add

def squareOperand (a b : U32) : Result U64 := do
  let left ← UScalar.add (core.convert.num.FromU64U32.from a) (core.convert.num.FromU64U32.from b)
  let base ← UScalar.add (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from aspis_core.field.P)
  let right ← UScalar.sub base (core.convert.num.FromU64U32.from b)
  UScalar.mul left right

theorem squareOperand_success (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    ∃ product : U64, squareOperand a b = .ok product ∧
      product.val = (a.val+b.val)*(a.val+P-b.val) := by
  have p : P = 2147483647 := rfl
  obtain ⟨left, hl, hvl⟩ := add_success (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from b) (by rw [widen_value, widen_value]; omega)
  rw [widen_value, widen_value] at hvl
  obtain ⟨base, ht, hvt⟩ := add_success (core.convert.num.FromU64U32.from a)
    (core.convert.num.FromU64U32.from aspis_core.field.P)
    (by rw [widen_value, widen_value, source_P_value]; omega)
  rw [widen_value, widen_value, source_P_value] at hvt
  obtain ⟨right, hr, hvr⟩ := sub_success base (core.convert.num.FromU64U32.from b)
    (by rw [widen_value, hvt]; omega)
  rw [hvt, widen_value] at hvr
  have hproduct : left.val*right.val < 2^64 := by
    have hleft : left.val < 2^32 := by rw [hvl]; omega
    have hright : right.val < 2^32 := by rw [hvr]; omega
    have h := Nat.mul_lt_mul_of_lt_of_lt hleft hright
    exact h
  obtain ⟨product, hp, hvp⟩ := mul_success left right hproduct
  refine ⟨product, ?_, ?_⟩
  · simp only [squareOperand, hl, ht, hr, hp, bind_tc_ok]
  · simpa only [hvl, hvr] using hvp

theorem generated_square_graph (x : aspis_core.field.CM31) :
    aspis_core.field.CM31.square x = (do
      let product ← squareOperand x.a x.b
      let real ← aspis_core.field.M31.reduce_u64 product
      let ab ← aspis_core.field.M31.mul x.a x.b
      let imag ← aspis_core.field.M31.double ab
      Result.ok ⟨real, imag⟩) := by
  simp only [aspis_core.field.CM31.square, squareOperand, lift,
    bind_tc_ok, bind_assoc_eq]
  rfl

theorem generated_square_words (x : aspis_core.field.CM31)
    (ha : x.a.val < P) (hb : x.b.val < P) :
    ∃ z : aspis_core.field.CM31, aspis_core.field.CM31.square x = .ok z ∧
      z.a.val = ((x.a.val+x.b.val)*(x.a.val+P-x.b.val))%P ∧
      z.b.val = ((x.a.val*x.b.val)%P + (x.a.val*x.b.val)%P)%P ∧
      z.a.val < P ∧ z.b.val < P := by
  obtain ⟨product, hp, hvp⟩ := squareOperand_success x.a x.b ha hb
  obtain ⟨real, hr, hvr, hcr⟩ := generated_wrapper_mod product
  obtain ⟨ab, hab, hvab, hcab⟩ := generated_mul_mod x.a x.b
  obtain ⟨imag, hi, hvi, hci⟩ := generated_double_mod ab hcab
  refine ⟨⟨real, imag⟩, ?_, ?_, ?_, hcr, hci⟩
  · rw [generated_square_graph]
    simp only [hp, hr, hab, hi, bind_tc_ok]
  · simpa only [hvp] using hvr
  · simpa only [hvab] using hvi

#print axioms squareOperand_success
#print axioms generated_square_graph
#print axioms generated_square_words
end AspisV8R17.GeneratedCM31Square
