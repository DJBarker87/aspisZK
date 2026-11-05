import NHX_FinalFold
import NHX_Powers7Edge
import NHM_LoopDomain
set_option autoImplicit false
namespace NHX_FinalLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells := Array NE 7#usize
abbrev State := NHI_RangeProgress.Range×NE

def body (parts powers : Cells) (s : State) : Result (ControlFlow State NE) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done s.2)
 | some kind=>do
  let part ← Array.index_usize parts kind
  let power ← Array.index_usize powers kind
  let sum ← NHX_FinalFold.cell s.2 power part
  ok (.cont (next,sum))

theorem step (parts powers : Cells) (s : State) :
 FIo_Native.weights.Weights.pair_loop17.body parts powers s.1 s.2=body parts powers s := by
 unfold FIo_Native.weights.Weights.pair_loop17.body body NHX_FinalFold.cell
 simp only [FIo_Native.trace.value,bind_tc_ok,bind_assoc_eq]

theorem progress (parts powers : Cells) (s t : State) (run : body parts powers s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some kind=>
  obtain ⟨part,hp,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨power,hk,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨sum,hs,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  have same:=ControlFlow.cont.inj (Result.ok.inj run)
  rw [←same]
  exact (NHI_RangeProgress.some_next s.1 next kind hn).2

theorem decreases (parts powers : Cells) (s t : State) (run : body parts powers s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,active⟩:=progress parts powers s t run
 have hv:=congrArg (fun x : Usize=>x.val) last
 omega

def reference (parts powers : Cells) := NHI_CountedLoop.unroll (body parts powers) 8
 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero)

theorem source (parts powers : Cells) :
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} parts powers NHI_Scalar.zero=
 reference parts powers := by
 unfold FIo_Native.weights.Weights.pair_loop17 reference
 have same:(fun s : State=>FIo_Native.weights.Weights.pair_loop17.body parts powers s.1 s.2)=body parts powers :=
  funext (step parts powers)
 rw [same]
 exact NHI_CountedLoop.agrees (body parts powers) (fun s=>s.1.end.val-s.1.start.val)
  (decreases parts powers) 8 _ (by change (7:Nat)-0<8;omega)

#print axioms step
#print axioms progress
#print axioms decreases
#print axioms source
end NHX_FinalLoop
