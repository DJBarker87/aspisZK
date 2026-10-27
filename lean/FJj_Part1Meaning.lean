import FJg_Part1Final
import FJj_ScaleModel
import FJj_HighReference
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_Part1Meaning
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE wide)
abbrev FE := OraclePortCheckpointAbiC5.E
abbrev FK := OraclePortCheckpointAbiC5.K
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv
/-- Complete installed original-point meaning on the SAME literal semantic
alpha, parsed message, and actual two-fold alpha reads, in the actual final
sum's array alongside part0. No free model tensor or local call law is assumed. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (alpha : Slice E) (f : Slice U8) (kappa out : E)
    (hc : FJc_WeightArray.canonical (FJg_LiteralTensor.source semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (folds : Slice.len (FIo_Install.toSlice alpha)=2#usize) (len : f.val.length=2048)
    (halpha : ∀ x∈(FIo_Install.toSlice alpha).val,FIo_WideValues.Canon x)
    (run : FIo_Install.pair r w alpha f kappa=ok (.Ok out)) :
    ∃ (nativeOut a0 a1 : NE) (low : Array NE 16#usize) (parts k : Array NE 7#usize),
      @FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
        (FIo_Install.toWeights w) (FIo_Install.toSlice alpha) f (FIo_Install.toE kappa)=ok (.Ok nativeOut) ∧
      FIo_Install.fromE nativeOut=out ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 0#usize=ok a0 ∧
      Slice.index_usize (FIo_Install.toSlice alpha) 1#usize=ok a1 ∧
      FIo_ArrayCanon.Holds low ∧
      FIo_Native.weights.powers 7#usize (FIo_Install.toE kappa)=ok k ∧
      FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts k
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok nativeOut ∧
      FIp_ArrayValue.value parts 0=FJc_InactiveValue.sumPrefix f low 12 ∧
      FIp_ArrayValue.value parts 1=RoundPairing.dot (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
        (RoundPairing.dualFold (n:=64) (AspisR1CurrentWide.Proof.decodeWide (wide a1))
          (RoundPairing.dualFold (n:=256) (AspisR1CurrentWide.Proof.decodeWide (wide a0))
            (fun j=>algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded (FJg_LiteralTensor.source semAlpha)) j)))) := by
  obtain ⟨nativeOut,a0,a1,ap0,ap1,common,partials,row,coeff,low0,low1,low,parts,k,
    hn,he,h0,h1,hp0,hp1,hcom,vcom,vp,hr,hd4,hd0,hd1,lc,hk,hsum,v0,v1⟩ :=
    FJg_Part1Final.value r semAlpha z w alpha f kappa out hc hw folds len halpha run
  have ca0 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 0#usize a0 halpha h0
  have ca1 := FJc_SliceCanonical.read (FIo_Install.toSlice alpha) 1#usize a1 halpha h1
  have scale0 := FJj_ScaleModel.value semAlpha z w hc hw 0 row low0 hr hd0 a0 ap0 ca0 hp0
  have scale1 := FJj_ScaleModel.value semAlpha z w hc hw 1 row low1 hr hd1 a1 ap1 ca1 hp1
  have high := FJj_HighReference.value semAlpha z w hc hw f common partials vcom vp row coeff hr hd4
  refine ⟨nativeOut,a0,a1,low,parts,k,hn,he,h0,h1,lc,hk,hsum,v0,?_⟩
  rw [v1,scale0,scale1,high]
  have tensor : (fun j=>algebraMap FK FE (tensorPoint (FJf_ModelPoint.decoded (FJg_LiteralTensor.source semAlpha)) j))=
      FJd_PointReference.tensor (FJg_LiteralTensor.factors semAlpha) := by
    funext j
    exact (FJg_LiteralTensor.value semAlpha j).symm
  rw [tensor,RoundPairing.dot]
  simp_rw [FJg_DualTensor.value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms value
end AspisR1.FJj_Part1Meaning
end
