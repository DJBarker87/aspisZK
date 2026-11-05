import NHX_HighDomain
import NHX_FieldResults
import NHM_LoopDomain
import NHM_ArrayPreserve
set_option autoImplicit false
namespace NHX_CommonDomain
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells:=Array NQ 16#usize
abbrev State:=NHI_RangeProgress.Range×Cells
abbrev W:=FIo_Native.weights.Weights

def body (w:W) (s:State):=FIo_Native.weights.Weights.pair_loop1.body w s.1 s.2

theorem row2 (w:W) (hf:NHI_TensorOuterStep.Factors w)
 (a:Array (Array NQ 4#usize) 5#usize) (b:Array NQ 4#usize)
 (ha:Array.index_usize w.factors 0#usize=ok a) (hb:Array.index_usize a 2#usize=ok b) :
 NHI_CellCanon.array b := by
 rw [NHI_ScalarDomain.index w.factors 0#usize (by decide)] at ha
 cases Result.ok.inj ha
 rw [NHI_ScalarDomain.index _ 2#usize (by decide)] at hb
 cases Result.ok.inj hb
 exact hf 0 (by decide) 2 (by decide)

theorem row3 (w:W) (hf:NHI_TensorOuterStep.Factors w)
 (a:Array (Array NQ 4#usize) 5#usize) (b:Array NQ 4#usize)
 (ha:Array.index_usize w.factors 0#usize=ok a) (hb:Array.index_usize a 3#usize=ok b) :
 NHI_CellCanon.array b := by
 rw [NHI_ScalarDomain.index w.factors 0#usize (by decide)] at ha
 cases Result.ok.inj ha
 rw [NHI_ScalarDomain.index _ 3#usize (by decide)] at hb
 cases Result.ok.inj hb
 exact hf 0 (by decide) 3 (by decide)

theorem preserves (w:W) (hf:NHI_TensorOuterStep.Factors w) (s t:State)
 (hs:NHI_CellCanon.array s.2) (run:body w s=ok (.cont t)) : NHI_CellCanon.array t.2 := by
 unfold body FIo_Native.weights.Weights.pair_loop1.body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨i,hi,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a1,ha1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,hq,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨i1,hi1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a2,ha2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a3,ha3,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have c0:=NHM_ArrayCanon.read canonQ a1 i q (row2 w hf a a1 ha ha1) hq
  have c1:=NHM_ArrayCanon.read canonQ a2 i1 q1 (row3 w hf a a2 ha ha2) hq1
  have cp:=NHX_FieldResults.qm_mul q q1 q2 c0 c1 hq2
  have co:=NHM_ArrayPreserve.canonical canonQ s.2 a3 j q2 hs cp ha3
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact co

theorem all_calls (w:W) (hf:NHI_TensorOuterStep.Factors w) (s:State)
 (hs:NHI_CellCanon.array s.2) : NHM_LoopDomain.all (body w)
 (fun s=>NHI_CellCanon.array s.2) 17 s :=
 NHM_LoopDomain.invariant (body w) (fun s=>NHI_CellCanon.array s.2)
 (fun s t hs run=>preserves w hf s t hs run) 17 s hs

#print axioms row2
#print axioms row3
#print axioms preserves
#print axioms all_calls
end NHX_CommonDomain
