import NIG_BothBranches
import NHX_FieldResults
import NHI_ForwardRange
set_option autoImplicit false
namespace NIG_LibraLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells:=Array NE 7#usize
abbrev Libra:=Array NE 4#usize
abbrev State:=NHI_RangeProgress.Range×Cells

def window (f:Slice U8) (libra:Libra) (j:Usize) (parts:Cells):Result Cells:=do
 let before←Array.index_usize parts 4#usize
 let coefficient←FIo_Native.weights.field f j
 let weight←Array.index_usize libra j
 let product←FIo_Native.aspis_core.field.wide_exact.WideExact.mul coefficient weight
 let after←FIo_Native.aspis_core.field.wide_exact.WideExact.add before product
 Array.update parts 4#usize after

def body (f:Slice U8) (libra:Libra) (s:State):Result (ControlFlow State Cells):=do
 let (o,next)←core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some j=>do let out←window f libra j s.2;ok (.cont (next,out))

theorem step (f:Slice U8) (libra:Libra) (s:State):
 FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2=body f libra s:=by
 unfold FIo_Native.weights.Weights.pair_loop16.body body window
 simp only [bind_assoc_eq]
 apply congrArg (fun k=>core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1 >>= k)
 funext it
 rcases it with ⟨o,next⟩
 cases o <;> rfl

theorem progress (f:Slice U8) (libra:Libra) (s t:State)
 (run:body f libra s=ok (.cont t)):
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val:=by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some j=>
  obtain ⟨out,ho,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact (NHI_RangeProgress.some_next s.1 next j hn).2

theorem decreases (f:Slice U8) (libra:Libra) (s t:State)
 (run:body f libra s=ok (.cont t)):
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val:=by
 obtain ⟨last,inc,active⟩:=progress f libra s t run
 have hv:=congrArg (fun x:Usize=>x.val) last
 omega

def reference (f:Slice U8) (libra:Libra) (parts:Cells):=
 NHI_CountedLoop.unroll (body f libra) 5 ({start:=0#usize,«end»:=4#usize},parts)

theorem source (f:Slice U8) (libra:Libra) (parts:Cells):
 FIo_Native.weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f parts libra=
 reference f libra parts:=by
 unfold FIo_Native.weights.Weights.pair_loop16 reference
 have same:(fun s:State=>FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2)=body f libra:=funext (step f libra)
 rw [same]
 exact NHI_CountedLoop.agrees (body f libra) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f libra) 5 _ (by change (4:Nat)-0<5;omega)
#print axioms step
#print axioms progress
#print axioms decreases
#print axioms source
end NIG_LibraLoop
