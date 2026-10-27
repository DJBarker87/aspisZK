import RPu_FJm_AbsorptionTrace
import RPu_FJm_AbsorptionHighReference
import RPu_FJg_ScalarValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_AbsorptionArithmetic
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low FJm_AbsorptionScale.factors

theorem value (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (f : Slice U8) (common : Array NQ 16#usize) (partials : Array NE 4#usize)
    (vcom : ∀ j,j<16 → FJf_QMArray.value common j=FJf_CommonCell.model (FJg_LiteralTensor.source semAlpha) j)
    (vp : FJg_PartialsValue.Values f common partials 4) (cp : FIo_ArrayCanon.Holds partials)
    (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (before after : Array NE 7#usize)
    (run : FIo_Native.weights.shared_high partials (FIo_Install.toWeights w) ap0 ap1 before=ok (.Ok (),after)) :
    FIp_ArrayValue.value after 3=
      FJg_DualTensor.low (fun s=>algebraMap FK FE (FJm_AbsorptionScale.factors semAlpha 0 s)) (decodeWide (wide a0))*
      FJg_DualTensor.low (fun s=>algebraMap FK FE (FJm_AbsorptionScale.factors semAlpha 1 s)) (decodeWide (wide a1))*
      (∑ i : Fin 64,FJc_InactiveCoefficientsModel.field f i.val*
        FJg_TensorProduct.high (fun d s=>algebraMap FK FE (FJm_AbsorptionScale.factors semAlpha d s)) i) := by
  obtain ⟨row,coeff,low0,low1,high,s0,s1,scale,value,base,hr,h4,hh,h0,hs0,h1,hs1,hm,hv,hu⟩ :=
    FJm_AbsorptionTrace.reached (FIo_Install.toWeights w) partials ap0 ap1 before after run
  have cc := (FJm_AbsorptionDigit.value semAlpha z w hc hw 4#usize (by decide) row coeff hr h4).1
  have vh := FJg_HighValue.four partials coeff cp cc high hh
  have cp0 := (FIp_PowersValue.powers 4#usize a0 ap0 ha0 hp0).1
  have cp1 := (FIp_PowersValue.powers 4#usize a1 ap1 ha1 hp1).1
  have sv0 := FJg_ScalarValue.value ap0 low0 cp0 s0 hs0
  have sv1 := FJg_ScalarValue.value ap1 low1 cp1 s1 hs1
  have mv := FIo_WideMulValues.mul s0 s1 scale sv0.1 sv1.1 hm
  have vv := FIo_WideMulValues.mul scale high value mv.1 vh.1 hv
  have sm0 := FJm_AbsorptionScale.value semAlpha z w hc hw 0#usize (by decide) row low0 hr h0 a0 ap0 ha0 hp0
  have sm1 := FJm_AbsorptionScale.value semAlpha z w hc hw 1#usize (by decide) row low1 hr h1 a1 ap1 ha1 hp1
  have iz : (⟨(0#usize).val,by decide⟩ : Fin 5)=0 := by decide
  have io : (⟨(1#usize).val,by decide⟩ : Fin 5)=1 := by decide
  rw [iz] at sm0
  rw [io] at sm1
  rw [FJc_ArrayUpdateValue.value base after 3#usize value 3 hu,if_pos (by rfl),vv.2,mv.2,
    sv0.2,sv1.2,sm0,sm1,vh.2,FJm_AbsorptionHighReference.value semAlpha z w hc hw f common partials vcom vp row coeff hr h4]
#print axioms value
end AspisR1.FJm_AbsorptionArithmetic
end
