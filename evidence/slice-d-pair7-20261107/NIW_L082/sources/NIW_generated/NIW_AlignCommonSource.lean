import NIW_AlignCommonCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignCommonSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_CommonChain

theorem source (w : W) (hf : NHI_TensorOuterStep.Factors w)
 (cells : CommonCells) (hc : NHI_CellCanon.array cells) :
 let observed := NIW_AlignCommonCollect.collect w 17 ({start:=0#usize,«end»:=16#usize},cells)
 FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w cells=observed.1 ∧
 NIW_AlignFieldReply.Produced observed.1 (fun out=>
  Trace w 17 ({start:=0#usize,«end»:=16#usize},cells) out ∧ out.1=w ∧ NHI_CellCanon.array out.2) := by
 have trace := NIW_AlignCommonCollect.trace w hf 17
  ({start:=0#usize,«end»:=16#usize},cells) rfl (by change (0:Nat)≤16;omega) hc
  (by change (16:Nat)-0<17;omega)
 cases result : (NIW_AlignCommonCollect.collect w 17 ({start:=0#usize,«end»:=16#usize},cells)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | div => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at trace
  have run : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w cells=ok out := by
   rw [NIG_CommonLoop.common_source]
   exact NIT_CommonChain.interpreted w hf 17 _ out trace
  have post := NIG_CommonPost.source w hf cells hc out run
  simp only [result,NIW_AlignFieldReply.Produced]
  exact ⟨run,trace,post⟩

#print axioms source
end AspisR1.NIW_AlignCommonSource
