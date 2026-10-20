import TerminalV4ReducerV1
import TerminalV4TowerAddV1

/-!
Symbolic port of the old CM31 cross-operand and current multiplication proof to
freshly extracted field functions using the full Aeneas runtime.  No projected
runtime declarations are imported or introduced here.
-/
set_option autoImplicit false

namespace AspisR1.TerminalV4CM31Mul

open Aeneas.Std Result Error
open AspisR1.TerminalV4ReducerOps
open AspisR1.TerminalV4TowerAdd

abbrev CM := AspisR1SelectedMaskProbe.field.CM31
abbrev M31 := AspisR1SelectedMaskProbe.field.M31

def realWord (a b c d : Nat) := ((a*c)%P + P - (b*d)%P)%P

def imagWord (a b c d : Nat) :=
  ((((a+b)*(c+d))%P + P - (a*c)%P)%P + P - (b*d)%P)%P

theorem widen_value (x : M31) :
    (Aeneas.Std.core.convert.num.FromU64U32.from x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  apply BitVec.toNat_setWidth_of_le
  decide

def crossOperand (a b c d : M31) : Result U64 := do
  let left ← UScalar.add (Aeneas.Std.core.convert.num.FromU64U32.from a)
    (Aeneas.Std.core.convert.num.FromU64U32.from b)
  let right ← UScalar.add (Aeneas.Std.core.convert.num.FromU64U32.from c)
    (Aeneas.Std.core.convert.num.FromU64U32.from d)
  UScalar.mul left right

theorem crossOperand_success (a b c d : M31)
    (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (hc : c.val < 2147483647) (hd : d.val < 2147483647) :
    ∃ product : U64, crossOperand a b c d = .ok product ∧
      product.val = (a.val+b.val)*(c.val+d.val) := by
  have hab : a.val + b.val < 2^32 := by omega
  have hcd : c.val + d.val < 2^32 := by omega
  have hleft :
      (Aeneas.Std.core.convert.num.FromU64U32.from a).val +
      (Aeneas.Std.core.convert.num.FromU64U32.from b).val < 2^64 := by
    rw [widen_value, widen_value]
    omega
  have hright :
      (Aeneas.Std.core.convert.num.FromU64U32.from c).val +
      (Aeneas.Std.core.convert.num.FromU64U32.from d).val < 2^64 := by
    rw [widen_value, widen_value]
    omega
  obtain ⟨left, hl, hvl⟩ := AspisR1.TerminalV4ReducerOps.add_success _ _ hleft
  obtain ⟨right, hr, hvr⟩ := AspisR1.TerminalV4ReducerOps.add_success _ _ hright
  rw [widen_value, widen_value] at hvl hvr
  have hprod : left.val * right.val < 2^64 := by
    rw [hvl, hvr]
    calc
      (a.val + b.val) * (c.val + d.val) < (2^32) * (2^32) :=
        Nat.mul_lt_mul_of_lt_of_lt hab hcd
      _ = 2^64 := by norm_num
  obtain ⟨product, hp, hvp⟩ := AspisR1.TerminalV4ReducerOps.mul_success left right hprod
  refine ⟨product, ?_, ?_⟩
  · simp only [crossOperand, hl, hr, bind_tc_ok, hp]
  · simpa only [hvl, hvr] using hvp

/-- The source-shaped cross-operand fragment used by current `field.CM31.mul`.
The surrounding two M31 products and following reductions remain separate. -/
def generatedCrossFragment (self rhs : CM) : Result U64 := do
  let i := self.a
  let i1 ← lift (Aeneas.Std.core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (Aeneas.Std.core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (Aeneas.Std.core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (Aeneas.Std.core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  .ok i10

private theorem bind_return_word (r : Result U64) :
    (do let x ← r; .ok x) = r := by
  cases r <;> rfl

theorem generatedCrossFragment_eq (self rhs : CM) :
    generatedCrossFragment self rhs = crossOperand self.a self.b rhs.a rhs.b := by
  simp only [generatedCrossFragment, crossOperand, Aeneas.Std.lift,
    bind_tc_ok, bind_return_word]
  rfl

theorem generatedCrossFragment_success (self rhs : CM)
    (ha : self.a.val < 2147483647) (hb : self.b.val < 2147483647)
    (hc : rhs.a.val < 2147483647) (hd : rhs.b.val < 2147483647) :
    ∃ product : U64, generatedCrossFragment self rhs = .ok product ∧
      product.val = (self.a.val+self.b.val)*(rhs.a.val+rhs.b.val) := by
  rw [generatedCrossFragment_eq]
  exact crossOperand_success _ _ _ _ ha hb hc hd

theorem generated_mul_graph (x y : CM) :
    AspisR1SelectedMaskProbe.field.CM31.mul x y = (do
      let m0 ← AspisR1SelectedMaskProbe.field.M31.mul x.a y.a
      let m1 ← AspisR1SelectedMaskProbe.field.M31.mul x.b y.b
      let product ← generatedCrossFragment x y
      let m2 ← AspisR1SelectedMaskProbe.field.M31.reduce_u64 product
      let low ← AspisR1SelectedMaskProbe.field.M31.sub m0 m1
      let high0 ← AspisR1SelectedMaskProbe.field.M31.sub m2 m0
      let high ← AspisR1SelectedMaskProbe.field.M31.sub high0 m1
      Result.ok ⟨low, high⟩) := by
  simp only [AspisR1SelectedMaskProbe.field.CM31.mul,
    generatedCrossFragment, lift, bind_tc_ok, bind_assoc_eq]

theorem current_mul_words (x y : CM)
    (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z : CM,
      AspisR1SelectedMaskProbe.field.CM31.mul x y = .ok z ∧
      CanonicalCM z ∧
      z.a.val = realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = imagWord x.a.val x.b.val y.a.val y.b.val := by
  obtain ⟨m0, h0, hv0, hc0⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.a y.a
  obtain ⟨m1, h1, hv1, hc1⟩ := AspisR1.TerminalV4Reducer.current_mul_mod x.b y.b
  obtain ⟨product, hp, hvp⟩ := generatedCrossFragment_success x y hx.1 hx.2 hy.1 hy.2
  obtain ⟨m2, h2, hv2, hc2⟩ := AspisR1.TerminalV4Reducer.current_wrapper_mod product
  rw [hvp] at hv2
  obtain ⟨low, hl, hvl, hcl⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod m0 m1 hc0 hc1
  obtain ⟨high0, hh0, hvh0, hch0⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod m2 m0 hc2 hc0
  obtain ⟨high, hh, hvh, hch⟩ := AspisR1.TerminalV4M31AddSub.current_sub_mod high0 m1 hch0 hc1
  refine ⟨⟨low, high⟩, ?_, ⟨hcl, hch⟩, ?_, ?_⟩
  · rw [generated_mul_graph]
    simp only [h0, h1, hp, h2, hl, hh0, hh, bind_tc_ok]
  · simpa only [realWord, hv0, hv1] using hvl
  · simpa only [imagWord, hvh0, hv2, hv0, hv1] using hvh

#print axioms widen_value
#print axioms crossOperand_success
#print axioms generatedCrossFragment_eq
#print axioms generatedCrossFragment_success
#print axioms generated_mul_graph
#print axioms current_mul_words

end AspisR1.TerminalV4CM31Mul
