import NHM_DotPacket
import NHI_PartialDotLoop
set_option autoImplicit false
namespace NHM_PartialDot
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev State := NHI_PartialDotLoop.State
abbrev Dot := NHM_DotPacket.Dot
abbrev NE := NHM_DotPacket.NE
abbrev NQ := NHM_DotPacket.NQ

def body (bytes : Slice U8) (common : Array NQ 16#usize) (offset : Usize) (s : State) :
 Result (ControlFlow State (core.result.Result NE FIo_Native.verifier.Error)) := do
 let (index,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match index with
 | none =>
  let out ← FIo_Native.fast_pairing.EbyKDot.finish s.2
  ok (.done (core.result.Result.Ok out))
 | some j =>
  let x ← FIo_Native.weights.field bytes (NHI_PartialIndex.index offset j)
  let q ← Array.index_usize common j
  let (reply,after) ← NHM_DotPacket.push s.2 x q
  match reply with
  | .Ok _ => ok (.cont (next,after))
  | .Err _ => ok (.done (core.result.Result.Err FIo_Native.verifier.Error.Parse))

theorem step (bytes : Slice U8) (common : Array NQ 16#usize) (offset : Usize) (s : State) :
 NHI_PartialDotLoop.body bytes common offset s=body bytes common offset s := by
 unfold NHI_PartialDotLoop.body FIo_Native.weights.partial_dot_loop.body body
 simp only [lift,bind_tc_ok,NHI_PartialIndex.index,NHM_DotPacket.source]
 rfl

def reference (bytes : Slice U8) (common : Array NQ 16#usize) (offset : Usize) := do
 let initial ← FIo_Native.fast_pairing.EbyKDot.new
 NHI_CountedLoop.unroll (body bytes common offset) 17
  ({start:=0#usize,«end»:=16#usize},initial)

theorem cohort (bytes : Slice U8) (common : Array NQ 16#usize) (offset : Usize) :
 FIo_Native.weights.partial_dot bytes common offset=reference bytes common offset := by
 rw [NHI_PartialDotLoop.source]
 unfold reference
 have bodies : NHI_PartialDotLoop.body bytes common offset=body bytes common offset :=
  funext (step bytes common offset)
 rw [bodies]

/-- A native successful window preserves count=index and remains within sixteen calls. -/
theorem invariant (bytes : Slice U8) (common : Array NQ 16#usize) (offset : Usize)
 (s t : State) (same : s.2.count.val=s.1.start.val) (last : s.1.end.val=16)
 (run : body bytes common offset s=ok (.cont t)) :
 t.2.count.val=t.1.start.val ∧ t.1.end.val=16 ∧ t.2.count.val≤16 := by
 rw [←step] at run
 obtain ⟨he,hi,hc,active⟩ := NHI_PartialDotLoop.progress bytes common offset s t run
 have hev := congrArg (fun x : Usize=>x.val) he
 constructor
 · omega
 constructor <;> omega

#print axioms step
#print axioms cohort
#print axioms invariant
end NHM_PartialDot
