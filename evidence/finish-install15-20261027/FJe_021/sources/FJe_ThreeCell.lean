import FJe_ThreeLimbTotal
import FJb_M31Scalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_ThreeCell
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open AspisV8R17.RawReducer (P)
def source (w0 w1 w2 : NQ) (c0 c1 c2 : U32) : Result NQ := do
  let m0 ← state_only_poseidon.interpolate_three_constant_limb w0.c0.a w1.c0.a w2.c0.a c0 c1 c2
  let m1 ← state_only_poseidon.interpolate_three_constant_limb w0.c0.b w1.c0.b w2.c0.b c0 c1 c2
  let real ← field.CM31.new m0 m1
  let m2 ← state_only_poseidon.interpolate_three_constant_limb w0.c1.a w1.c1.a w2.c1.a c0 c1 c2
  let m3 ← state_only_poseidon.interpolate_three_constant_limb w0.c1.b w1.c1.b w2.c1.b c0 c1 c2
  let imag ← field.CM31.new m2 m3
  pure ({c0 := real,c1 := imag} : NQ)

theorem source_success (w0 w1 w2 : NQ) (c0 c1 c2 : U32)
    (hw0 : Canon w0) (hw1 : Canon w1) (hw2 : Canon w2)
    (hc0 : c0.val < P) (hc1 : c1.val < P) (hc2 : c2.val < P) :
    ∃ out : NQ, source w0 w1 w2 c0 c1 c2 = .ok out ∧ Canon out ∧
      decode out = decode w0 * (c0.val : K) + decode w1 * (c1.val : K) +
        decode w2 * (c2.val : K) := by
  obtain ⟨m0,h0,hcan0,hmodel0⟩ := FJe_ThreeLimbTotal.value
    w0.c0.a w1.c0.a w2.c0.a c0 c1 c2 hw0.1.1 hw1.1.1 hw2.1.1 hc0 hc1 hc2
  obtain ⟨m1,h1,hcan1,hmodel1⟩ := FJe_ThreeLimbTotal.value
    w0.c0.b w1.c0.b w2.c0.b c0 c1 c2 hw0.1.2 hw1.1.2 hw2.1.2 hc0 hc1 hc2
  obtain ⟨m2,h2,hcan2,hmodel2⟩ := FJe_ThreeLimbTotal.value
    w0.c1.a w1.c1.a w2.c1.a c0 c1 c2 hw0.2.1 hw1.2.1 hw2.2.1 hc0 hc1 hc2
  obtain ⟨m3,h3,hcan3,hmodel3⟩ := FJe_ThreeLimbTotal.value
    w0.c1.b w1.c1.b w2.c1.b c0 c1 c2 hw0.2.2 hw1.2.2 hw2.2.2 hc0 hc1 hc2
  let out : NQ := ⟨⟨m0,m1⟩,⟨m2,m3⟩⟩
  refine ⟨out,?_,⟨⟨hcan0,hcan1⟩,⟨hcan2,hcan3⟩⟩,?_⟩
  · simp only [source,h0,h1,h2,h3,field.CM31.new,bind_tc_ok]
    rfl
  · ext <;> simp [decode,ExtractedMaskQM31Exact.decode,out,
      FIv_NativeArithmetic.qm,FIv_NativeArithmetic.cm,hmodel0,hmodel1,hmodel2,hmodel3]

#print axioms source_success
end AspisR1.FJe_ThreeCell
end
