import NLV_RunLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLV_Emitted
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NLJ_Tx1
open CheckpointBytes5Effect (Code)
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult

def emittedTry {A : Type} (r : core.result.Result A verifier.Error) (k : A → Code Out) : Code Out := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val => k val
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    (alloc.vec.Vec U8) (core.convert.FromSame verifier.Error) residual
theorem try_run {A : Type} (h : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (r : core.result.Result A verifier.Error) (k : A → Code Out) (before : SdkC_Source.Log) :
 SdkC_Source.run h (emittedTry r k) before =
 match r with
 | .Err e => (ok (.Err e),before)
 | .Ok a => SdkC_Source.run h (k a) before := by
 cases r <;> rfl
#print axioms try_run

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
   emittedTry r (fun pair => suffix_finishPending cfg i p pair.1 pair.2)

def suffix_pending (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (geom : verifier.QueryGeometry) : Code Out := do
   let r ← (ops cfg).op18 (alloc.vec.Vec.deref a.weights)
   emittedTry r (fun pending => suffix_query cfg i g p a geom pending)

def suffix_geometry (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   let r ← (ops cfg).op19 p.queries 0#usize i.k
   emittedTry r (fun geom => suffix_pending cfg i g p a geom)

def suffix_markMerkle (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) : Code Out := do
   verifier.mark none (verifier.Phase.Merkle 0#usize)
   suffix_geometry cfg i g p a

def suffix_batch0 (cfg : Configuration) (i : Input) (g : Scratch) (p : verifier.Prepared) (a : verifier.Accumulator) (root : Root) : Code Out := do
   let r ← SdkC_BatchSource.currentCode i.hashv i.proof p root
   emittedTry r (fun _ => suffix_markMerkle cfg i g p a)

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
   emittedTry r (fun a => suffix_markPrepare cfg i g p a)

def suffix_prepare (cfg : Configuration) (i : Input) (g : Scratch) : Code Out := do
   let (r,after) ← SdkD_PrepareLower.lower (SdkD_PrepareSource.code
    (Op5T_Concrete.current {cfg.base with op16:=Tx1Q_Install.writer})
    cfg.boundaries cfg.std i.digest i.publicValue i.proof () g)
   emittedTry r (fun p => suffix_accumulator cfg i after p)

def suffix_zero (cfg : Configuration) (i : Input)  : Code Out := do
   let zero ← aspis_core.field.wide_exact.WideExact.ZERO (ops cfg)
   suffix_prepare cfg i (Array.repeat 29#usize zero)

def suffix_markParsed (cfg : Configuration) (i : Input)  : Code Out := do
   verifier.mark none verifier.Phase.Parsed
   suffix_zero cfg i

def suffix_scan (cfg : Configuration) (i : Input)  : Code Out := do
   let r ← (ops cfg).op4 i.proof
   emittedTry r (fun _ => suffix_markParsed cfg i)

def suffix_parse (cfg : Configuration) (i : Input)  : Code Out := do
   let r ← (ops cfg).op3 i.proof
   emittedTry r (fun _ => suffix_scan cfg i)

def suffix_guard (cfg : Configuration) (i : Input)  : Code Out := do
   if i.k != compact.SPLIT then pure (.Err verifier.Error.Parse)
   else suffix_parse cfg i

/-- Structural identity with the adopted emitted body, including every Try
residual and aborting pure step. No native cut is inferred. -/
theorem initial_source (cfg : Configuration) (i : Input) :
 suffix_guard cfg i = GExp_FirstCode.code cfg.base cfg.boundaries cfg.std
 i.hashv i.digest i.publicValue i.publicBytes i.proof i.k := by
 unfold suffix_guard suffix_parse suffix_scan suffix_markParsed suffix_zero suffix_prepare suffix_accumulator suffix_markPrepare suffix_foldedSlice suffix_foldedCopy suffix_foldedUnwrap suffix_batch0 suffix_markMerkle suffix_geometry suffix_pending suffix_query suffix_finishPending suffix_checkpoint suffix_markCheckpoint suffix_returned GExp_FirstCode.code
 dsimp only [emittedTry,ops]
 simp only [Bind.bind,Pure.pure]
 repeat' first
 | rfl
 | (apply NLV_Algebra.same; intro reply; cases reply)
 | (split)
#print axioms initial_source
end AspisR1.NLV_Emitted
end
