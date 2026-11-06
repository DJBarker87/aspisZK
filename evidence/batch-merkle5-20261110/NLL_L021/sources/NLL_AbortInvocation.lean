import NLL_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- An in-progress child is a terminal parent outcome, not a fabricated
returned cut. `answered` excludes the pending request. The parent frame and
child's complete mutable footprint remain available at the abort boundary. -/
structure Pending where
 parts : Slice (Slice U8)
 answered : History
 parent : Frame
 childScratch : reference.Scratch

/-- Abort-only runtime calls have no Err reply and no suffix constructor.
NJS batch_leaf's syscall boundary is before deduplication. The terminal
verifier abort uses the CLOSED child packet with its SAME current arrays. -/
inductive AbortLoop (H : Bytes → State) (proof : Slice U8) (root : Root)
 (batch : Nat) (kind lo n slot : Usize) : Frame → List Event → Pending → Prop where
 | leaf (f : Frame) (more : f.position<n) :
   AbortLoop H proof root batch kind lo n slot f []
     ⟨Port4B_LeafCode.input kind (view H proof lo (key f)),[],advance f f.scratch,f.scratch⟩
 | verify (f : Frame) (done : ¬f.position<n)
   (well : OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys f.scratch))
   (fits : OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)≤OraclePortSelectedDraft.capacity (3*batch+kind.val))
   (padding : MultiproofConePadding.scan
     (4*(OraclePortSelectedDraft.capacity (3*batch+kind.val)-OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))
     ((MultiproofConeCanonical.bytesOf (nodeView H proof slot).val).drop
       (32*OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))=true)
   (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest))
   (q : NJP_RowModel.Request) (pending : NJP_RowModel.Scratch)
   (child : NJV_AbortEntry.Invocation (NJP_RequestTransport.hash (MultiproofConePhysicalTransport.rawOracle H)) root
     (MultiproofConeSlotTail.prefixNodes (nodeView H proof slot) (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch)))
     (NJV_EntryABI.initial f.scratch.idx f.scratch.val f.scratch.n) queries q pending) :
   AbortLoop H proof root batch kind lo n slot f []
     ⟨NJP_RequestTransport.address q,NJV_AdoptedObservation.history queries,f,NJP_ScratchCarrier.emitted pending⟩
 | next (f : Frame) (t : reference.Scratch) (more : f.position<n)
   (step : reference.leaf_step f.scratch (Port4B_NativeLeaf.decodedIndex (key f))
     (digest H proof kind lo f)=ok (some t)) (events : List Event) (pending : Pending)
   (tail : AbortLoop H proof root batch kind lo n slot (advance f t) events pending) :
   AbortLoop H proof root batch kind lo n slot f (event H proof kind lo f::events) pending

def AbortInvocation (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Root) (batch kind : Usize) (idx : Indices) (val : Values)
 (events : List Event) (pending : Pending) : Prop :=
 ∃ rest,events=.entry (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) (entryKeys H raw batch.val kind)::rest ∧
 AbortLoop H proof root batch.val kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
   ⟨entryKeys H raw batch.val kind,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ rest pending
end NLL
end
