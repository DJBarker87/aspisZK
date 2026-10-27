import RPv_FJr_RegularKindTrace
import RPv_FJj_TensorTwo
import RPv_FJj_ByteDotFinal
import RPv_FJm_VecLens
import RPv_FJg_ScalarValue
import RPt_FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_RegularCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)

theorem value [FIo_Native.Allocation] (w : FIo_Native.weights.Weights)
    (variant : w.variant=.S2) (kind idx : Usize) (large : ¬kind<4#usize)
    (index : Usize.wrapping_sub kind 2#usize=idx)
    (row : Array (Array NQ 4#usize) 5#usize) (hr : Array.index_usize w.factors idx=ok row)
    (rc : ∀ digit∈row.val,FJf_QMArray.canon digit)
    (alpha : Slice NE) (f : Slice U8) (ap0 ap1 : Array NE 4#usize)
    (cp0 : FIo_ArrayCanon.Holds ap0) (cp1 : FIo_ArrayCanon.Holds ap1)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (cs : FJj_QMSlice.canon (alloc.vec.Vec.deref scratch)) (cb : FIo_ArrayCanon.Holds before)
    (run : FIo_Native.weights.process_kind w kind alpha f 2#usize 64#usize ap0 ap1 scratch before=
      ok (.Ok (),scratchOut,after)) :
    FJj_QMSlice.canon (alloc.vec.Vec.deref scratchOut) ∧ FIo_ArrayCanon.Holds after := by
  obtain ⟨input,tensor,back,row',low0,low1,s0,s1,scale,dotValue,nativeValue,dot,dotOut,
    hderef,htensor,hr',h0,hs0,h1,hs1,hm,hback,hnew,hpush,hfinish,hvalue,hwrite⟩ :=
    FJr_RegularKindTrace.reached w variant kind idx large index alpha f 64#usize ap0 ap1 scratch scratchOut before after run
  have er : row'=row := Result.ok.inj (hr'.symm.trans hr)
  subst row'
  have lens := FJm_VecLens.value scratch input back hderef tensor
  have ci : FJj_QMSlice.canon input := by rw [lens.1];exact cs
  have backValue : alloc.vec.Vec.deref scratchOut=tensor := by rw [hback];exact lens.2
  rw [backValue] at hpush
  have tv := FJj_TensorTwo.value w idx row hr rc input tensor ci htensor
  have dv := FJj_ByteDotFinal.value f tensor tv.1 dot dotOut dotValue hnew hpush hfinish
  have sv0 := FJg_ScalarValue.value ap0 low0 cp0 s0 hs0
  have sv1 := FJg_ScalarValue.value ap1 low1 cp1 s1 hs1
  have mv := FIo_WideMulValues.mul s0 s1 scale sv0.1 sv1.1 hm
  have vv := FIo_WideMulValues.mul scale dotValue nativeValue mv.1 dv.1 hvalue
  exact ⟨by rw [backValue];exact tv.1,FIo_ArrayCanon.update before after kind nativeValue cb vv.1 hwrite⟩

#print axioms value
end AspisR1.FJr_RegularCanonical
end
