import AspisV8R17.GeneratedM31Sub

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::CM31}::mul"]
def aspis_core.field.CM31.mul
  (self : aspis_core.field.CM31) (rhs : aspis_core.field.CM31) :
  Result aspis_core.field.CM31
  := do
  let m0 ← aspis_core.field.M31.mul self.a rhs.a
  let m1 ← aspis_core.field.M31.mul self.b rhs.b
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
  let m2 ← aspis_core.field.M31.reduce_u64 i10
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedCM31Mul
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedM31Mul GeneratedM31Sub
open UnsignedCM31Cross RawReducer

def realWord (a b c d : Nat) := ((a*c)%P + P - (b*d)%P)%P
def imagWord (a b c d : Nat) :=
  ((((a+b)*(c+d))%P + P - (a*c)%P)%P + P - (b*d)%P)%P

theorem generated_mul_graph (x y : aspis_core.field.CM31) :
    aspis_core.field.CM31.mul x y = (do
      let m0 ← aspis_core.field.M31.mul x.a y.a
      let m1 ← aspis_core.field.M31.mul x.b y.b
      let product ← generatedCrossFragment x y
      let m2 ← aspis_core.field.M31.reduce_u64 product
      let low ← aspis_core.field.M31.sub m0 m1
      let high0 ← aspis_core.field.M31.sub m2 m0
      let high ← aspis_core.field.M31.sub high0 m1
      Result.ok ⟨low, high⟩) := by
  simp only [aspis_core.field.CM31.mul, generatedCrossFragment, lift,
    bind_tc_ok, bind_assoc_eq]

/-- Exact canonical word-level result of the complete current generated caller.
Field-algebra normalization and full protocol callers are separate obligations. -/
theorem generated_mul_words (x y : aspis_core.field.CM31)
    (ha : x.a.val < P) (hb : x.b.val < P)
    (hc : y.a.val < P) (hd : y.b.val < P) :
    ∃ z : aspis_core.field.CM31, aspis_core.field.CM31.mul x y = .ok z ∧
      z.a.val = realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = imagWord x.a.val x.b.val y.a.val y.b.val ∧
      z.a.val < P ∧ z.b.val < P := by
  obtain ⟨m0, h0, hv0, hc0⟩ := generated_mul_mod x.a y.a
  obtain ⟨m1, h1, hv1, hc1⟩ := generated_mul_mod x.b y.b
  obtain ⟨product, hp, hvp⟩ := generatedCrossFragment_success x y ha hb hc hd
  obtain ⟨m2, h2, hv2, hc2⟩ := generated_wrapper_mod product
  rw [hvp] at hv2
  obtain ⟨low, hl, hvl, hcl⟩ := generated_sub_mod m0 m1 hc0 hc1
  obtain ⟨high0, hh0, hvh0, hch0⟩ := generated_sub_mod m2 m0 hc2 hc0
  obtain ⟨high, hh, hvh, hch⟩ := generated_sub_mod high0 m1 hch0 hc1
  refine ⟨⟨low, high⟩, ?_, ?_, ?_, hcl, hch⟩
  · rw [generated_mul_graph]
    simp only [h0, h1, hp, h2, hl, hh0, hh, bind_tc_ok]
  · simpa only [realWord, hv0, hv1] using hvl
  · simpa only [imagWord, hvh0, hv2, hv0, hv1] using hvh

#print axioms generated_mul_graph
#print axioms generated_mul_words
end AspisV8R17.GeneratedCM31Mul
