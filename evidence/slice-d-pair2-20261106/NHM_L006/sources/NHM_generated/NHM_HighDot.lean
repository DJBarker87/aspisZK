import NHM_DotPacket
import NHI_HighDotLoop
set_option autoImplicit false
namespace NHM_HighDot
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev State := NHI_HighDotLoop.State
abbrev Dot := NHM_DotPacket.Dot
abbrev NE := NHM_DotPacket.NE
abbrev NQ := NHM_DotPacket.NQ

def body (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize) (s : State) : Result (ControlFlow State (core.result.Result NE FIo_Native.verifier.Error)) := do
 let (index,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match index with
 | none =>
  let out ← FIo_Native.fast_pairing.EbyKDot.finish s.2
  ok (.done (core.result.Result.Ok out))
 | some j =>
  let x ← Array.index_usize partials j
  let q ← Array.index_usize coeffs j
  let (reply,after) ← NHM_DotPacket.push s.2 x q
  match reply with
  | .Ok _ => ok (.cont (next,after))
  | .Err _ => ok (.done (core.result.Result.Err FIo_Native.verifier.Error.Parse))

theorem step (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize) (s : State) :
 NHI_HighDotLoop.body partials coeffs s=body partials coeffs s := by
 unfold NHI_HighDotLoop.body FIo_Native.weights.high_dot_loop.body body
 simp only [NHM_DotPacket.source]

def reference (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize) := do
 let initial ← FIo_Native.fast_pairing.EbyKDot.new
 NHI_CountedLoop.unroll (body partials coeffs) 5
  ({start:=0#usize,«end»:=4#usize},initial)

theorem cohort (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize) :
 FIo_Native.weights.high_dot partials coeffs=reference partials coeffs := by
 rw [NHI_HighDotLoop.source]
 unfold reference
 have bodies : NHI_HighDotLoop.body partials coeffs=body partials coeffs :=
  funext (step partials coeffs)
 rw [bodies]

/-- A native successful window preserves count=index and remains within four calls. -/
theorem invariant (partials : Array NE 4#usize) (coeffs : Array NQ 4#usize)
 (s t : State) (same : s.2.count.val=s.1.start.val) (last : s.1.end.val=4)
 (run : body partials coeffs s=ok (.cont t)) :
 t.2.count.val=t.1.start.val ∧ t.1.end.val=4 ∧ t.2.count.val≤4 := by
 rw [←step] at run
 obtain ⟨he,hi,hc,active⟩ := NHI_HighDotLoop.progress partials coeffs s t run
 constructor
 · omega
 constructor <;> omega

#print axioms step
#print axioms cohort
#print axioms invariant
end NHM_HighDot
