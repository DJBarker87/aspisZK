import NFP_TraceBack
import NFS_QueryOps
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_TraceBack
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def model (ops : Ops) (accum : U32 → E → Result (verifier.Accumulator × verifier.BatchedWeights)) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) : M Out :=
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
  let (a1,b1) ← eval (accum node folded1)
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

/-- Congruence is isolated on an abstract dictionary, so no concrete Ops
record is normalized while the monadic continuation is inferred. -/
theorem model_congr (ops : Ops) (first second : U32 → E → Result (verifier.Accumulator × verifier.BatchedWeights))
 (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots)
 (same : ∀ alpha folded,ops.op16 alpha values inverse=ok folded → ∀ node,first node folded=second node folded) :
 model ops first p a geometry pending inverse values = model ops second p a geometry pending inverse values := by
 unfold model
 congr 1
 funext alpha
 congr 1
 funext ignored
 apply eval_bind
 intro folded h
 simp only [same alpha folded h]

def run (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) : M Out :=
 model (NFS_QueryOps.installed base) (fun node value=>NFS_AccumInstall.run p a node value pending)
  p a geometry pending inverse values

theorem source (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (inverse : Inverse) (values : Dots) :
 model (NFP_ObserverErasure.erase ops)
  (fun node value=>verifier.accumulate_batched_with_node (NFP_ObserverErasure.erase ops) p a node value pending)
  p a geometry pending inverse values = NFP_TraceBack.run ops p a geometry pending inverse values := rfl

theorem installed (base : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverse : Inverse) (values : Dots) (input : NFS_AccumDomain.Input p a pending) :
 run base p a geometry pending inverse values =
 NFP_TraceBack.run (NFS_QueryOps.installed base) p a geometry pending inverse values := by
 rw [←source]
 apply model_congr
 intro alpha folded h node
 have canonical := NFS_AccumDomain.line alpha values inverse folded h
 exact (NFS_AccumInstall.installed (NFS_QueryOps.base base)
  p a node folded pending input canonical).trans (NFS_QueryOps.accumulation base p a node folded pending).symm
#print axioms eval_bind
#print axioms model_congr
#print axioms source
#print axioms installed
end AspisR1.NFS_TraceBack
end
