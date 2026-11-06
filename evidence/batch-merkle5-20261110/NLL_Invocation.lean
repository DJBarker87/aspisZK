import NLL_State
set_option autoImplicit false
noncomputable section
namespace NLL
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def emptyView : Slice U8 := ⟨[],by simp⟩
def view (H : Bytes → State) (proof : Slice U8) (lo : Usize) (key : U64) : Slice U8 :=
 match (NKV_ConcreteChildren.ops H).op2 proof (Port4B_NativeLeaf.openingIndex lo key) with
 | .ok value => value
 | _ => emptyView

def nodeView (H : Bytes → State) (proof : Slice U8) (slot : Usize) : Slice U8 :=
 match (NKV_ConcreteChildren.ops H).op3 proof slot with
 | .ok value => value
 | _ => emptyView

def key (f : Frame) : U64 := f.keys.val[f.position.val]!
def digest (H : Bytes → State) (proof : Slice U8) (kind lo : Usize) (f : Frame) : Root :=
 encodeState (H (flatten (Port4B_LeafCode.input kind (view H proof lo (key f)))))
def event (H : Bytes → State) (proof : Slice U8) (kind lo : Usize) (f : Frame) : Event :=
 .leaf f.position (key f) (view H proof lo (key f)) (digest H proof kind lo f)
def advance (f : Frame) (s : reference.Scratch) : Frame :=
 ⟨f.keys,s,Usize.wrapping_add f.position 1#usize⟩

/-- Reviewed parent cuts with CLOSED child implementations installed. The
leaf cut uses the native dedup/append control formula on arbitrary scratch;
its association is inherited NKB/NKL cuts and NKV_LeafStep, not a free Ops
or child-success input. Terminal.verify contains the SAME nested native
invocation, never a selected scratch seed. All returning errors stop here.
The loop's key stream and domain are proved by the root from entry. -/
inductive Loop (H : Bytes → State) (proof : Slice U8) (root : Root)
 (batch : Nat) (kind lo n slot : Usize) : Frame → List Event → Answer → Prop where
 | reject (f : Frame) (more : f.position<n)
   (step : reference.leaf_step f.scratch (Port4B_NativeLeaf.decodedIndex (key f))
     (digest H proof kind lo f)=ok none) :
   Loop H proof root batch kind lo n slot f [event H proof kind lo f]
     (.Err .Merkle,f.scratch.idx,f.scratch.val)
 | next (f : Frame) (t : reference.Scratch) (more : f.position<n)
   (step : reference.leaf_step f.scratch (Port4B_NativeLeaf.decodedIndex (key f))
     (digest H proof kind lo f)=ok (some t)) (events : List Event) (out : Answer)
   (tail : Loop H proof root batch kind lo n slot (advance f t) events out) :
   Loop H proof root batch kind lo n slot f (event H proof kind lo f::events) out
 | terminal (f : Frame) (done : ¬f.position<n) (events : List Event) (out : Answer)
   (tail : Terminal H root batch kind.val (nodeView H proof slot) f.scratch events out) :
   Loop H proof root batch kind lo n slot f events out

/-- Entry cut: actual key producer and actual sort are selected by their
CLOSED bodies. No separate array or independently chosen stream is supplied. -/
def entryKeys (H : Bytes → State) (raw : Array U32 22#usize) (batch : Nat) (kind : Usize) : Keys :=
 match (do let first ← (NKV_ConcreteChildren.ops H).op4 raw (NKB_KeyStream.lo batch) (NKB_KeyStream.count batch) kind
           (NKV_ConcreteChildren.ops H).op5 first (NKB_KeyStream.count batch)) with
 | .ok keys => keys
 | _ => Array.repeat 16#usize 0#u64

def Invocation (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : Root) (batch kind : Usize) (idx : Indices) (val : Values)
 (events : List Event) (out : Answer) : Prop :=
 ∃ rest,events=.entry (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) (entryKeys H raw batch.val kind)::rest ∧
 Loop H proof root batch.val kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind)
   ⟨entryKeys H raw batch.val kind,NJV_EntryABI.initial idx val 0#usize,0#usize⟩ rest out
end NLL
end
