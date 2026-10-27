import RPv_FJr_RegularKindTrace
import RPv_FJr_RowTensor
import RPv_FJr_RowScale
import RPv_FJj_ByteDotFinal
import RPv_FJm_VecLens
import RPu_FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_RegularKindMeaning
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
open scoped BigOperators
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E
attribute [local irreducible] QuadraticAlgebra.instInv FJg_DualTensor.low

theorem value [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (variant : w.variant=.S2) (kind idx : Usize) (large : ¬kind<4#usize)
    (index : Usize.wrapping_sub kind 2#usize=idx)
    (row : Array (Array NQ 4#usize) 5#usize) (hr : Array.index_usize w.factors idx=ok row)
    (rc : ∀ digit∈row.val,FJf_QMArray.canon digit) (factors : Fin 5 → Fin 4 → FK)
    (rv : ∀ (d : Fin 5) (s : Fin 4),FJj_TensorPrefix.rowValue row d.val s.val=factors d s)
    (alpha : Slice NE) (f : Slice U8) (a0 a1 : NE) (ap0 ap1 : Array NE 4#usize)
    (ca0 : FIo_WideValues.Canon a0) (ca1 : FIo_WideValues.Canon a1)
    (hp0 : FIo_Native.weights.powers 4#usize a0=ok ap0)
    (hp1 : FIo_Native.weights.powers 4#usize a1=ok ap1)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (cs : FJj_QMSlice.canon (alloc.vec.Vec.deref scratch))
    (run : FIo_Native.weights.process_kind w kind alpha f 2#usize 64#usize ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    FJj_QMSlice.canon (alloc.vec.Vec.deref scratchOut) ∧
    FIp_ArrayValue.value after kind.val=RoundPairing.dot
      (fun i : Fin 64=>FJc_InactiveCoefficientsModel.field f i.val)
      (RoundPairing.dualFold (n:=64) (decodeWide (wide a1))
        (RoundPairing.dualFold (n:=256) (decodeWide (wide a0))
          (FJd_PointReference.tensor (fun d s=>algebraMap FK FE (factors d s))))) := by
  obtain ⟨input,tensor,back,row',low0,low1,s0,s1,scale,dotValue,nativeValue,dot,dotOut,
    hderef,htensor,hr',h0,hs0,h1,hs1,hm,hback,hnew,hpush,hfinish,hvalue,hwrite⟩ :=
    FJr_RegularKindTrace.reached w variant kind idx large index alpha f 64#usize ap0 ap1 scratch scratchOut before after run
  have er : row'=row := Result.ok.inj (hr'.symm.trans hr)
  subst row'
  have lens := FJm_VecLens.value scratch input back hderef tensor
  have ci : FJj_QMSlice.canon input := by rw [lens.1];exact cs
  have backValue : alloc.vec.Vec.deref scratchOut=tensor := by rw [hback];exact lens.2
  rw [backValue] at hpush
  have tv := FJr_RowTensor.value w idx row hr rc factors rv input tensor ci htensor
  have dv := FJj_ByteDotFinal.value f tensor tv.1 dot dotOut dotValue hnew hpush hfinish
  have dvValue : decodeWide (wide dotValue)=∑ i : Fin 64,FJc_InactiveCoefficientsModel.field f i.val*
      FJg_TensorProduct.high (fun d s=>algebraMap FK FE (factors d s)) i := by
    rw [dv.2]
    apply Finset.sum_congr rfl
    intro i _
    rw [tv.2.2 i]
  have cp0 := (FIp_PowersValue.powers 4#usize a0 ap0 ca0 hp0).1
  have cp1 := (FIp_PowersValue.powers 4#usize a1 ap1 ca1 hp1).1
  have sv0 := FJg_ScalarValue.value ap0 low0 cp0 s0 hs0
  have sv1 := FJg_ScalarValue.value ap1 low1 cp1 s1 hs1
  have mv := FIo_WideMulValues.mul s0 s1 scale sv0.1 sv1.1 hm
  have vv := FIo_WideMulValues.mul scale dotValue nativeValue mv.1 dv.1 hvalue
  have sm0 := FJr_RowScale.value row low0 factors rv 0 0#usize rfl h0 a0 ap0 ca0 hp0
  have sm1 := FJr_RowScale.value row low1 factors rv 1 1#usize rfl h1 a1 ap1 ca1 hp1
  refine ⟨by rw [backValue];exact tv.1,?_⟩
  rw [FJc_ArrayUpdateValue.value before after kind nativeValue kind.val hwrite,if_pos rfl,
    vv.2,mv.2,sv0.2,sv1.2,sm0,sm1,dvValue,RoundPairing.dot]
  simp_rw [FJg_DualTensor.value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms value
end AspisR1.FJr_RegularKindMeaning
end
