import NIG_PairS2Body
import NIG_PairInputs
import NIG_PairValues
set_option autoImplicit false
noncomputable section
namespace NIQ_AllocationError
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem source (proof:Slice U8) (v:AspisR1Stage2.verifier.View)
 (p:AspisR1Stage2.verifier.Prepared) (a:AspisR1Stage2.verifier.Accumulator)
 (domain:NIG_FinishInput.Domain proof v p a) (w:FIo_Native.weights.Weights)
 (e:NP6_StdModel.ReserveError):
 letI:=FIo_Install.allocation (.Err e)
 FIo_Native.weights.Weights.pair w (FIo_Install.toSlice p.alpha.to_slice) v.final_message
  (FIo_Install.toE p.kappa)=ok (.Err .Allocation):=by
 letI:=FIo_Install.allocation (.Err e)
 rw [NIG_PairS2Body.source w p v.final_message (NIG_PairInputs.final_width proof v p a domain)]
 unfold NIG_PairS2Body.reference
 let alpha:=FIo_Install.toSlice p.alpha.to_slice
 have len:alpha.val.length=2:=by change (p.alpha.val.map FIo_Install.toE).length=2;rw [List.length_map,p.alpha.property];rfl
 let x:=alpha.val[0]'(by rw [len];decide)
 let y:=alpha.val[1]'(by rw [len];decide)
 have ix:Slice.index_usize alpha 0#usize=ok x:=by simp [Slice.index_usize,x,len]
 have iy:Slice.index_usize alpha 1#usize=ok y:=by simp [Slice.index_usize,y,len]
 have all:=NIG_PairInputs.alphas proof v p a domain
 have cx:canonE x:=all x (List.getElem_mem _)
 have cy:canonE y:=all y (List.getElem_mem _)
 obtain ⟨ap0,h0,_,_⟩:=NFW_PowersCohort.source 4#usize x cx
 obtain ⟨ap1,h1,_,_⟩:=NFW_PowersCohort.source 4#usize y cy
 dsimp only [alpha] at ix iy
 rw [ix]
 simp only [bind_tc_ok]
 rw [h0]
 simp only [bind_tc_ok]
 rw [iy]
 simp only [bind_tc_ok]
 rw [h1]
 simp only [bind_tc_ok]
 rw [NHI_FilledModel.qm]
 rfl
#print axioms source
end NIQ_AllocationError
