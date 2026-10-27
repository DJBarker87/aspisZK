import RPu_FJm_KindTwoTrace
import RPu_FJm_VecLens
import RPu_FJj_SuccessorDot
import RPu_FJj_SuccessorScale
import RPu_FJj_LiteralPointTensor
import RPu_FJg_ScalarValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_KindTwoArithmetic
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NQ NE wide)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
open scoped BigOperators
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low FJj_SuccessorHigh.factors

/-- Actual kind2 write. The later Pair continuation and scratch initialization
remain separate obligations; this is not the final-parts part2 theorem. -/
theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_WideValues.Canon a0) (ha1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (hs : FJj_QMSlice.canon (alloc.vec.Vec.deref scratch))
    (run : @FIo_Native.weights.process_kind (FIo_Install.allocation r) (FIo_Install.toWeights w)
      2#usize alpha f 2#usize 64#usize ap0 ap1 scratch before=ok (.Ok (),scratchOut,after)) :
    FIp_ArrayValue.value after 2=
      FJg_DualTensor.low (fun s=>algebraMap FK FE (FJj_SuccessorHigh.factors semAlpha 0 s)) (decodeWide (wide a0))*
      FJg_DualTensor.low (fun s=>algebraMap FK FE (FJj_SuccessorHigh.factors semAlpha 1 s)) (decodeWide (wide a1))*
      (∑ i : Fin 64,FJc_InactiveCoefficientsModel.field f i.val*
        FJg_TensorProduct.high (fun d s=>algebraMap FK FE (FJj_SuccessorHigh.factors semAlpha d s)) i) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  obtain ⟨input,tensor,back,row,low0,low1,s0,s1,scale,dotValue,nativeValue,dot,dotOut,
    hderef,htensor,hr,h0,hs0,h1,hs1,hm,hback,hnew,hpush,hfinish,hvalue,hwrite⟩ :=
    FJm_KindTwoTrace.reached (FIo_Install.toWeights w) variant alpha f 64#usize ap0 ap1 scratch scratchOut before after run
  have lens := FJm_VecLens.value scratch input back hderef tensor
  have ci : FJj_QMSlice.canon input := by rw [lens.1];exact hs
  have backValue : alloc.vec.Vec.deref scratchOut=tensor := by rw [hback];exact lens.2
  rw [backValue] at hpush
  have dv := FJj_SuccessorDot.value semAlpha z w hc hw row hr input tensor ci htensor
    f dot dotOut dotValue hnew hpush hfinish
  have cp0 := (FIp_PowersValue.powers 4#usize a0 ap0 ha0 hp0).1
  have cp1 := (FIp_PowersValue.powers 4#usize a1 ap1 ha1 hp1).1
  have sv0 := FJg_ScalarValue.value ap0 low0 cp0 s0 hs0
  have sv1 := FJg_ScalarValue.value ap1 low1 cp1 s1 hs1
  have mv := FIo_WideMulValues.mul s0 s1 scale sv0.1 sv1.1 hm
  have vv := FIo_WideMulValues.mul scale dotValue nativeValue mv.1 dv.1 hvalue
  have sm0 := FJj_SuccessorScale.value semAlpha z w hc hw 0#usize (by decide) row low0 hr h0 a0 ap0 ha0 hp0
  have sm1 := FJj_SuccessorScale.value semAlpha z w hc hw 1#usize (by decide) row low1 hr h1 a1 ap1 ha1 hp1
  have iz : (⟨(0#usize).val,by decide⟩ : Fin 5)=0 := by decide
  have io : (⟨(1#usize).val,by decide⟩ : Fin 5)=1 := by decide
  rw [iz] at sm0
  rw [io] at sm1
  rw [FJc_ArrayUpdateValue.value before after 2#usize nativeValue 2 hwrite,if_pos (by rfl),
    vv.2,mv.2,sv0.2,sv1.2,sm0,sm1,dv.2]

#print axioms value
end AspisR1.FJm_KindTwoArithmetic
end
