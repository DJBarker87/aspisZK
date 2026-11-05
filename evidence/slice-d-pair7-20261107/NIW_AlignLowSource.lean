import NIW_AlignLowCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLowSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_LowChain

theorem source (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1)
 (cells : LowCells) (hc : canonical cells) :
 let observed := NIW_AlignLowCollect.collect ap0 ap1 17 ({start:=0#usize,«end»:=16#usize},cells)
 FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 cells=observed.1 ∧
 NIW_AlignFieldReply.Produced observed.1 (fun out=>
  Trace ap0 ap1 17 ({start:=0#usize,«end»:=16#usize},cells) out ∧ canonical out) := by
 have trace := NIW_AlignLowCollect.trace ap0 ap1 h0 h1 17
  ({start:=0#usize,«end»:=16#usize},cells) rfl (by change (0:Nat)≤16;omega) hc
  (by change (16:Nat)-0<17;omega)
 cases result : (NIW_AlignLowCollect.collect ap0 ap1 17 ({start:=0#usize,«end»:=16#usize},cells)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | div => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at trace
  have run : FIo_Native.weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1 cells=ok out := by
   rw [NIG_LowLoop.low_source]
   exact NIT_LowChain.interpreted ap0 ap1 17 _ out trace.1
  simp only [result,NIW_AlignFieldReply.Produced]
  exact ⟨run,trace⟩

#print axioms source
end AspisR1.NIW_AlignLowSource
