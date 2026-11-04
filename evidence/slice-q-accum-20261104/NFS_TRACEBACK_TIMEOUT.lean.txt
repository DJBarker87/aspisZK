import NFP_TraceBack
import NFS_QueryOps
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_TraceBack
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) : M Out :=
 let ops := NFS_QueryOps.installed base
 do
  let we6 ← eval (Array.index_usize p.alpha 1#usize)
  mark (.line we6 values inverse)
  let folded1 ← eval (ops.op16 we6 values inverse)
  let i10 ← eval (lift (Usize.wrapping_mul 2#usize a.next))
  let i11 ← eval (lift (Usize.wrapping_add i10 1#usize))
  mark (.trace 10#u16 i11 folded1)
  eval (ops.op15 10#u16 i11 folded1)
  let i12 ← eval (lift (Usize.wrapping_sub a.next geometry.start))
  let z ← eval (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) geometry.line_z i12)
  mark (.product z z)
  let product ← eval (ops.op7 z z)
  mark (.double product)
  let doubled ← eval (ops.op8 product)
  mark .one
  let one ← eval ops.op5
  mark (.subtract doubled one)
  let node ← eval (ops.op6 doubled one)
  mark (.accumulate p a node folded1 pending)
  let (a1,b1) ← eval (NFS_AccumInstall.run p a node folded1 pending)
  eval (ops.op19 none (.Query a.next))
  pure (.Ok (a1,b1))

/-- Only successful values invoke a continuation; failed/divergent prefixes
retain their exact observations without a fabricated suffix. -/
theorem eval_bind {A B : Type} (r : Result A) (first second : A → M B)
 (same : ∀ a,r=ok a → first a=second a) :
 (eval r >>= first)=(eval r >>= second) := by
 cases h:r with
 | fail e => rfl
 | div => rfl
 | ok a => exact congrArg (fun t : M B=>NFI_TraceResult.M.mk t.result ([]++t.cuts)) (same a h)

theorem installed (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) (input : NFS_AccumDomain.Input p a pending) :
 run base p a geometry pending inverse values =
 NFP_TraceBack.run (NFS_QueryOps.installed base) p a geometry pending inverse values := by
 unfold run NFP_TraceBack.run
 congr 1
 funext alpha
 congr 1
 funext ignored
 apply eval_bind
 intro folded h
 have canonical := NFS_AccumDomain.line alpha values inverse folded h
 have child := fun node => (NFS_AccumInstall.installed (NFS_QueryOps.base base)
  p a node folded pending input canonical).trans (NFS_QueryOps.accumulation base p a node folded pending).symm
 simp only [child]
#print axioms eval_bind
#print axioms installed
end AspisR1.NFS_TraceBack
end
