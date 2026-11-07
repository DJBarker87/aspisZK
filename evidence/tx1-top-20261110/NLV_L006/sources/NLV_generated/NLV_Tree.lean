import NLV_Algebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Tree
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def suffix_returned (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) : Code Out := do
   pure (.Ok bytes)

def suffix_markCheckpoint (cfg : Configuration) (i : Input) (bytes : alloc.vec.Vec U8) : Code Out := do
   verifier.mark none verifier.Phase.CheckpointWrite
   suffix_returned cfg i bytes

def suffix_checkpoint (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   let bytes ← GExp_FirstCode.writerCode p a i.proof i.publicBytes
   suffix_markCheckpoint cfg i bytes

def suffix_finishPending (cfg : Configuration) (i : Input) (p : verifier.Prepared) (a : verifier.Accumulator) (pending : verifier.BatchedWeights) : Code Out := do
   let (weights,back) ← lift (alloc.vec.Vec.deref_mut a.weights)
   let after ← (ops cfg).op17 pending weights
   suffix_checkpoint cfg i p {a with weights:=back after}

def suffix_query (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) (pending : verifier.BatchedWeights) : Code Out := do
   let r ← (ops cfg).op7 i.proof p a g none geom pending i.k
   match r with
   | .Err e => pure (.Err e)
   | .Ok pair => suffix_finishPending cfg i p pair.1 pair.2

def suffix_pending (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) : Code Out := do
   let r ← (ops cfg).op18 (alloc.vec.Vec.deref a.weights)
   match r with
   | .Err e => pure (.Err e)
   | .Ok pending => suffix_query cfg i g p a geom pending

def suffix_geometry (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   let r ← (ops cfg).op19 p.queries 0#usize i.k
   match r with
   | .Err e => pure (.Err e)
   | .Ok geom => suffix_pending cfg i g p a geom

def suffix_markMerkle (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   verifier.mark none (verifier.Phase.Merkle 0#usize)
   suffix_geometry cfg i g p a

def suffix_batch0 (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root) : Code Out := do
   let r ← SdkC_BatchSource.currentCode i.hashv i.proof p root
   match r with
   | .Err e => pure (.Err e)
   | .Ok _ => suffix_markMerkle cfg i g p a

def suffix_foldedUnwrap (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (r : core.result.Result Root core.array.TryFromSliceError) : Code Out := do
   let root ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
   suffix_batch0 cfg i g p a root

def suffix_foldedCopy (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (slice : Slice U8) : Code Out := do
   let r ← core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice
   suffix_foldedUnwrap cfg i g p a r

def suffix_foldedSlice (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   let lo ← compact.OFF_FOLDED_ROOT (ops cfg)
   let hi ← compact.OFF_ROUND1 (ops cfg)
   let slice ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) i.proof {start:=lo,«end»:=hi}
   suffix_foldedCopy cfg i g p a slice

def suffix_markPrepare (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   verifier.mark none verifier.Phase.Prepare
   suffix_foldedSlice cfg i g p a

def suffix_accumulator (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) : Code Out := do
   let r ← (ops cfg).op20 transport.Variant.S2
   match r with
   | .Err e => pure (.Err e)
   | .Ok a => suffix_markPrepare cfg i g p a

def suffix_prepare (cfg : Configuration) (i : Input) (g : Scratch) : Code Out := do
   let (r,after) ← SdkD_PrepareLower.lower (SdkD_PrepareSource.code
    (Op5T_Concrete.current {cfg.base with op16:=Tx1Q_Install.writer})
    cfg.boundaries cfg.std i.digest i.publicValue i.proof () g)
   match r with
   | .Err e => pure (.Err e)
   | .Ok p => suffix_accumulator cfg i after p

def suffix_zero (cfg : Configuration) (i : Input)  : Code Out := do
   let zero ← aspis_core.field.wide_exact.WideExact.ZERO (ops cfg)
   suffix_prepare cfg i (Array.repeat 29#usize zero)

def suffix_markParsed (cfg : Configuration) (i : Input)  : Code Out := do
   verifier.mark none verifier.Phase.Parsed
   suffix_zero cfg i

def suffix_scan (cfg : Configuration) (i : Input)  : Code Out := do
   let r ← (ops cfg).op4 i.proof
   match r with
   | .Err e => pure (.Err e)
   | .Ok _ => suffix_markParsed cfg i

def suffix_parse (cfg : Configuration) (i : Input)  : Code Out := do
   let r ← (ops cfg).op3 i.proof
   match r with
   | .Err e => pure (.Err e)
   | .Ok _ => suffix_scan cfg i

def suffix_guard (cfg : Configuration) (i : Input)  : Code Out := do
   if i.k != compact.SPLIT then pure (.Err verifier.Error.Parse)
   else suffix_parse cfg i

def denote (cfg : Configuration) (s : NLJ_Tx1.State) : Code Out :=
 match s.locals with
 | .guard => suffix_guard cfg s.input
 | .parse => suffix_parse cfg s.input
 | .scan => suffix_scan cfg s.input
 | .markParsed => suffix_markParsed cfg s.input
 | .zero => suffix_zero cfg s.input
 | .prepare g => suffix_prepare cfg s.input g
 | .accumulator g p => suffix_accumulator cfg s.input g p
 | .markPrepare g p a => suffix_markPrepare cfg s.input g p a
 | .foldedSlice g p a => suffix_foldedSlice cfg s.input g p a
 | .foldedCopy g p a slice => suffix_foldedCopy cfg s.input g p a slice
 | .foldedUnwrap g p a r => suffix_foldedUnwrap cfg s.input g p a r
 | .batch0 g p a root => suffix_batch0 cfg s.input g p a root
 | .markMerkle g p a => suffix_markMerkle cfg s.input g p a
 | .geometry g p a => suffix_geometry cfg s.input g p a
 | .pending g p a geom => suffix_pending cfg s.input g p a geom
 | .query g p a geom pending => suffix_query cfg s.input g p a geom pending
 | .finishPending p a pending => suffix_finishPending cfg s.input p a pending
 | .checkpoint p a => suffix_checkpoint cfg s.input p a
 | .markCheckpoint bytes => suffix_markCheckpoint cfg s.input bytes
 | .returned bytes => suffix_returned cfg s.input bytes
end AspisR1.NLV_Tree
end
