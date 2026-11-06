import NLJ_Tx1State
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Tx1
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def nextOrError {A : Type} (s : State) (r : core.result.Result A verifier.Error) (k : A → Local) : Post :=
 match r with | .Err e => .inl (.Err e) | .Ok a => .inr (advance s (k a))
/-- Source-order transcription; its installed body slots are not a root-level
Ops hypothesis. OPEN087/081 remain explicit packet obligations. -/
def step (cfg : Configuration) (s : State) : Code Post := do
 let i := s.input
 let o := ops cfg
 match s.locals with
 | .guard =>
   if i.k != compact.SPLIT then pure (.inl (.Err verifier.Error.Parse))
   else pure (.inr (advance s .parse))
 | .parse =>
   let r ← o.op3 i.proof
   pure (nextOrError s r (fun _ => .scan))
 | .scan =>
   let r ← o.op4 i.proof
   pure (nextOrError s r (fun _ => .markParsed))
 | .markParsed =>
   verifier.mark none verifier.Phase.Parsed
   pure (.inr (advance s .zero))
 | .zero =>
   let zero ← aspis_core.field.wide_exact.WideExact.ZERO o
   pure (.inr (advance s (.prepare (Array.repeat 29#usize zero))))
 | .prepare g =>
   let (r,after) ← SdkD_PrepareLower.lower (SdkD_PrepareSource.code
    (Op5T_Concrete.current {cfg.base with op16:=Tx1Q_Install.writer})
    cfg.boundaries cfg.std i.digest i.publicValue i.proof () g)
   pure (nextOrError s r (fun p => .accumulator after p))
 | .accumulator g p =>
   let r ← o.op20 transport.Variant.S2
   pure (nextOrError s r (fun a => .markPrepare g p a))
 | .markPrepare g p a =>
   verifier.mark none verifier.Phase.Prepare
   pure (.inr (advance s (.foldedSlice g p a)))
 | .foldedSlice g p a =>
   let lo ← compact.OFF_FOLDED_ROOT o
   let hi ← compact.OFF_ROUND1 o
   let slice ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=lo,«end»:=hi}
   pure (.inr (advance s (.foldedCopy g p a slice)))
 | .foldedCopy g p a slice =>
   let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice
   pure (.inr (advance s (.foldedUnwrap g p a r)))
 | .foldedUnwrap g p a r =>
   let root ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
   pure (.inr (advance s (.batch0 g p a root)))
 | .batch0 g p a root =>
   let r ← SdkC_BatchSource.currentCode i.hashv i.proof p root
   pure (nextOrError s r (fun _ => .markMerkle g p a))
 | .markMerkle g p a =>
   verifier.mark none (verifier.Phase.Merkle 0#usize)
   pure (.inr (advance s (.geometry g p a)))
 | .geometry g p a =>
   let r ← o.op19 p.queries 0#usize i.k
   pure (nextOrError s r (fun geom => .pending g p a geom))
 | .pending g p a geom =>
   let r ← o.op18 (alloc.vec.Vec.deref a.weights)
   pure (nextOrError s r (fun pending => .query g p a geom pending))
 | .query g p a geom pending =>
   let r ← o.op7 i.proof p a g none geom pending i.k
   pure (nextOrError s r (fun pair => .finishPending p pair.1 pair.2))
 | .finishPending p a pending =>
   let (weights,back) ← lift (alloc.vec.Vec.deref_mut a.weights)
   let after ← o.op17 pending weights
   pure (.inr (advance s (.checkpoint p {a with weights:=back after})))
 | .checkpoint p a =>
   let bytes ← GExp_FirstCode.writerCode p a i.proof i.publicBytes
   pure (.inr (advance s (.markCheckpoint bytes)))
 | .markCheckpoint bytes =>
   verifier.mark none verifier.Phase.CheckpointWrite
   pure (.inr (advance s (.returned bytes)))
 | .returned bytes => pure (.inl (.Ok bytes))
end AspisR1.NLJ_Tx1
end
