import NHM_DotResult
import NHM_ArrayPreserve
set_option autoImplicit false
namespace NHM_SharedPartials
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev Cells := Array NE 4#usize
abbrev State := NHI_RangeProgress.Range × Cells
abbrev Reply := core.result.Result Cells FIo_Native.verifier.Error

def body (f : Slice U8) (common : Array NQ 16#usize) (s : State) : Result (ControlFlow State Reply) := do
 let (o,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match o with
 | none=>ok (.done (.Ok s.2))
 | some side=>do
  let r ← NHM_PartialDot.reference f common side
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue value=>do
   let after ← Array.update s.2 side value
   ok (.cont (next,after))
  | core.ops.control_flow.ControlFlow.Break residual=>do
   let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    Cells (core.convert.FromSame FIo_Native.verifier.Error) residual
   ok (.done r1)

theorem step (f : Slice U8) (common : Array NQ 16#usize) (s : State) :
 FIo_Native.weights.shared_partials_loop.body f common s.1 s.2=body f common s := by
 unfold FIo_Native.weights.shared_partials_loop.body body
 simp only [NHM_PartialDot.cohort]
 rfl

theorem progress (f : Slice U8) (common : Array NQ 16#usize) (s t : State)
 (run : body f common s=ok (.cont t)) :
 t.1.end=s.1.end ∧ t.1.start.val=s.1.start.val+1 ∧ s.1.start.val<s.1.end.val := by
 unfold body at run
 obtain ⟨⟨o,next⟩,hn,run⟩:=Port3_PushFrame.bind_success _ _ _ run
 cases o with
 | none=>cases run
 | some side=>
  obtain ⟨reply,hr,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases reply with
  | Err e=>cases run
  | Ok value=>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
   obtain ⟨after,ha,run⟩:=Port3_PushFrame.bind_success _ _ _ run
   have same:=ControlFlow.cont.inj (Result.ok.inj run)
   rw [←same]
   exact (NHI_RangeProgress.some_next s.1 next side hn).2

theorem decreases (f : Slice U8) (common : Array NQ 16#usize) (s t : State)
 (run : body f common s=ok (.cont t)) :
 t.1.end.val-t.1.start.val<s.1.end.val-s.1.start.val := by
 obtain ⟨last,inc,active⟩:=progress f common s t run
 have hv:=congrArg (fun x : Usize=>x.val) last
 omega

def reference (f : Slice U8) (common : Array NQ 16#usize) :=
 NHI_CountedLoop.unroll (body f common) 5
  ({start:=0#usize,«end»:=4#usize},Array.repeat 4#usize NHI_Scalar.zero)

/-- Four SAME calls s0..3 and first-error transport. Native parent association
still needs its own cuts and is not counted as a CLOSED row. -/
theorem cohort (f : Slice U8) (common : Array NQ 16#usize) :
 FIo_Native.weights.shared_partials f common=reference f common := by
 unfold FIo_Native.weights.shared_partials FIo_Native.weights.shared_partials_loop reference
 have same : (fun s : State=>FIo_Native.weights.shared_partials_loop.body f common s.1 s.2)=body f common := funext (step f common)
 rw [same]
 exact NHI_CountedLoop.agrees (body f common) (fun s=>s.1.end.val-s.1.start.val)
  (decreases f common) 5 _ (by change (4:Nat)-0<5;omega)

#print axioms step
#print axioms progress
#print axioms decreases
#print axioms cohort
end NHM_SharedPartials
