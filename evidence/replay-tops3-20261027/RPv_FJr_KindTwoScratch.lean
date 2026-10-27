import RPv_FJm_KindTwoTrace
import RPv_FJm_VecLens
import RPv_FJj_SuccessorRow
import RPv_FJj_TensorTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_KindTwoScratch
open Aeneas Aeneas.Std Result
open AspisR1Stage2 AspisR1Stage2.Stage2Finish
open FIo_FieldBridge (NE NQ)

theorem value (r : NP6_StdModel.Reservation) (semAlpha : Array K 10#usize)
    (z : Array aspis_core.circle.SecureCirclePoint 2#usize) (w : FIo_Install.W)
    (hc : FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ semAlpha))
    (hw : FIn_WeightsInstall.newWeights .S2 semAlpha z=ok (.Ok w))
    (alpha : Slice NE) (f : Slice U8) (ap0 ap1 : Array NE 4#usize)
    (scratch scratchOut : alloc.vec.Vec NQ) (before after : Array NE 7#usize)
    (cs : FJj_QMSlice.canon (alloc.vec.Vec.deref scratch))
    (run : @FIo_Native.weights.process_kind (FIo_Install.allocation r) (FIo_Install.toWeights w)
      2#usize alpha f 2#usize 64#usize ap0 ap1 scratch before=ok (.Ok (),scratchOut,after)) :
    FJj_QMSlice.canon (alloc.vec.Vec.deref scratchOut) := by
  letI := FIo_Install.allocation r
  obtain ⟨_,_,_,_,_,_,_,_,_,_,variant,_⟩ := FJc_InstalledParts.value .S2 semAlpha z w hw
  obtain ⟨input,tensor,back,row,low0,low1,s0,s1,scale,dotValue,nativeValue,dot,dotOut,
    hderef,htensor,hr,h0,hs0,h1,hs1,hm,hback,hnew,hpush,hfinish,hvalue,hwrite⟩ :=
    FJm_KindTwoTrace.reached (FIo_Install.toWeights w) variant alpha f 64#usize ap0 ap1 scratch scratchOut before after run
  have lens := FJm_VecLens.value scratch input back hderef tensor
  have ci : FJj_QMSlice.canon input := by rw [lens.1];exact cs
  have cr := FJj_SuccessorRow.value semAlpha z w hc hw row hr
  have tv := FJj_TensorTwo.value (FIo_Install.toWeights w) 1#usize row hr cr input tensor ci htensor
  rw [hback,lens.2]
  exact tv.1

#print axioms value
end AspisR1.FJr_KindTwoScratch
end
