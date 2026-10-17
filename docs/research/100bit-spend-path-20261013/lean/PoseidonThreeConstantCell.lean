import PoseidonThreeConstantLimbV4
import AspisR1.PoseidonFullRoundCellStep

/-! The four exact scalar source calls in an interpolated constant cell.
Array read/write binding belongs to the enclosing columns loop. -/
set_option autoImplicit false
namespace AspisR1.PoseidonThreeConstantCell
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (QM Canonical Decode Exact P)

def source (w0 w1 w2 : QM) (c0 c1 c2 : U32) : Result QM := do
  let m0 ← state_only_poseidon.interpolate_three_constant_limb w0.c0.a w1.c0.a w2.c0.a c0 c1 c2
  let m1 ← state_only_poseidon.interpolate_three_constant_limb w0.c0.b w1.c0.b w2.c0.b c0 c1 c2
  let real ← field.CM31.new m0 m1
  let m2 ← state_only_poseidon.interpolate_three_constant_limb w0.c1.a w1.c1.a w2.c1.a c0 c1 c2
  let m3 ← state_only_poseidon.interpolate_three_constant_limb w0.c1.b w1.c1.b w2.c1.b c0 c1 c2
  let imag ← field.CM31.new m2 m3
  pure ({c0 := real,c1 := imag} : QM)

theorem source_success (w0 w1 w2 : QM) (c0 c1 c2 : U32)
    (hw0 : Canonical w0) (hw1 : Canonical w1) (hw2 : Canonical w2)
    (hc0 : c0.val < P) (hc1 : c1.val < P) (hc2 : c2.val < P) :
    ∃ out : QM, source w0 w1 w2 c0 c1 c2 = .ok out ∧ Canonical out ∧
      Decode out = Decode w0 * (c0.val : Exact) + Decode w1 * (c1.val : Exact) +
        Decode w2 * (c2.val : Exact) := by
  obtain ⟨m0,h0,hcan0,hmodel0⟩ := AspisR1.PoseidonThreeConstantLimb.source_model
    w0.c0.a w1.c0.a w2.c0.a c0 c1 c2 hw0.1.1 hw1.1.1 hw2.1.1 hc0 hc1 hc2
  obtain ⟨m1,h1,hcan1,hmodel1⟩ := AspisR1.PoseidonThreeConstantLimb.source_model
    w0.c0.b w1.c0.b w2.c0.b c0 c1 c2 hw0.1.2 hw1.1.2 hw2.1.2 hc0 hc1 hc2
  obtain ⟨m2,h2,hcan2,hmodel2⟩ := AspisR1.PoseidonThreeConstantLimb.source_model
    w0.c1.a w1.c1.a w2.c1.a c0 c1 c2 hw0.2.1 hw1.2.1 hw2.2.1 hc0 hc1 hc2
  obtain ⟨m3,h3,hcan3,hmodel3⟩ := AspisR1.PoseidonThreeConstantLimb.source_model
    w0.c1.b w1.c1.b w2.c1.b c0 c1 c2 hw0.2.2 hw1.2.2 hw2.2.2 hc0 hc1 hc2
  let out : QM := ⟨⟨m0,m1⟩,⟨m2,m3⟩⟩
  refine ⟨out,?_,⟨⟨hcan0,hcan1⟩,⟨hcan2,hcan3⟩⟩,?_⟩
  · simp only [source,h0,h1,h2,h3,field.CM31.new,bind_tc_ok]
    rfl
  · ext <;> simp [Decode,AspisR1.ExtractedMaskQM31Exact.decode,out,
      hmodel0,hmodel1,hmodel2,hmodel3]

#print axioms source_success
end AspisR1.PoseidonThreeConstantCell
