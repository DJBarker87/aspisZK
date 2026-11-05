import NIG_CommonLoop
import NIG_LoopPost
set_option autoImplicit false
namespace NIG_CommonPost
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
open NHX_CommonDomain

theorem done (w:W) (s:State) (out:W×Cells)
 (hs:NHI_CellCanon.array s.2) (run:body w s=ok (.done out)) :
 out.1=w ∧ NHI_CellCanon.array out.2 := by
 unfold body FIo_Native.weights.Weights.pair_loop1.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>
  have same:=ControlFlow.done.inj (Result.ok.inj run)
  rw [←same]
  exact ⟨rfl,hs⟩
 | some j=>
  obtain ⟨x0,h0,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x1,h1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x2,h2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x3,h3,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x4,h4,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x5,h5,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x6,h6,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x7,h7,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨x8,h8,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run

theorem source (w:W) (hf:NHI_TensorOuterStep.Factors w) (cells:Cells)
 (hc:NHI_CellCanon.array cells) (out:W×Cells)
 (run:FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w cells=ok out) :
 out.1=w ∧ NHI_CellCanon.array out.2 := by
 rw [NIG_CommonLoop.common_source] at run
 exact NIG_LoopPost.post (body w) (fun s=>NHI_CellCanon.array s.2)
  (fun out=>out.1=w ∧ NHI_CellCanon.array out.2)
  (fun s t hs step=>preserves w hf s t hs step)
  (done w) 17 _ out hc run
#print axioms done
#print axioms source
end NIG_CommonPost
