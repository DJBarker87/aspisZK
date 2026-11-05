import NHM_DotPacket
import NHI_ByteProductsLoop
set_option autoImplicit false
namespace NHM_ByteProducts
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev State := NHI_ByteProductsLoop.State
abbrev Dot := NHM_DotPacket.Dot
abbrev NE := NHM_DotPacket.NE
abbrev NQ := NHM_DotPacket.NQ

def body (bytes : Slice U8) (scratch : Slice NQ) (s : State) : Result (ControlFlow State (core.result.Result Unit FIo_Native.verifier.Error × Dot)) := do
 let (index,next) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize s.1
 match index with
 | none => ok (.done (core.result.Result.Ok (),s.2))
 | some j =>
  let x ← FIo_Native.weights.field bytes j
  let q ← Slice.index_usize scratch j
  let (reply,after) ← NHM_DotPacket.push s.2 x q
  match reply with
  | .Ok _ => ok (.cont (next,after))
  | .Err _ => ok (.done (core.result.Result.Err FIo_Native.verifier.Error.Parse,after))

theorem step (bytes : Slice U8) (scratch : Slice NQ) (s : State) :
 NHI_ByteProductsLoop.body bytes scratch s=body bytes scratch s := by
 unfold NHI_ByteProductsLoop.body FIo_Native.weights.push_byte_products_loop.body body
 simp only [NHM_DotPacket.source]
 rfl

def reference (bytes : Slice U8) (scratch : Slice NQ) (initial : Dot) (n : Usize) :=
 NHI_CountedLoop.unroll (body bytes scratch) (n.val+1)
  ({start:=0#usize,«end»:=n},initial)

theorem cohort (bytes : Slice U8) (scratch : Slice NQ) (initial : Dot) (n : Usize) :
 FIo_Native.weights.push_byte_products initial bytes scratch n=reference bytes scratch initial n := by
 rw [NHI_ByteProductsLoop.source]
 unfold reference
 have bodies : NHI_ByteProductsLoop.body bytes scratch=body bytes scratch :=
  funext (step bytes scratch)
 rw [bodies]

/-- A native successful window preserves count=index and remains within the caller bound. -/
theorem invariant (bytes : Slice U8) (scratch : Slice NQ)
 (s t : State) (same : s.2.count.val=s.1.start.val) (n : Nat) (last : s.1.end.val=n)
 (run : body bytes scratch s=ok (.cont t)) :
 t.2.count.val=t.1.start.val ∧ t.1.end.val=n ∧ t.2.count.val≤n := by
 rw [←step] at run
 obtain ⟨he,hi,hc,active⟩ := NHI_ByteProductsLoop.progress bytes scratch s t run
 have hev := congrArg (fun x : Usize=>x.val) he
 constructor
 · omega
 constructor <;> omega

#print axioms step
#print axioms cohort
#print axioms invariant
end NHM_ByteProducts
