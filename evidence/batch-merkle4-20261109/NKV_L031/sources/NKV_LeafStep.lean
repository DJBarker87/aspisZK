import NKV_ActiveStep
set_option autoImplicit false
noncomputable section
namespace NKV_LeafStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_LoopTransport MultiproofConeRef

def project (s : reference.Scratch) (pos : Usize) : Option reference.Scratch → ControlFlow State Out
 | none => .done (s.idx,s.val,.Err .Merkle,false)
 | some t => .cont (t.idx,t.val,t.n,pos)

theorem project_source (s : reference.Scratch) (pos : Usize) (out : Option reference.Scratch) :
 NKV_ActiveStep.restore (Port4B_LeafStep.project s pos out)=project s pos out := by
 cases out <;> rfl

/-- Full source leaf-step association, with arbitrary initial suffix cells and
all duplicate/append/rejection arms. These local child reads are to be proved
at SAME inputs by the concrete parent, not retained as a positive root premise. -/
theorem source (base : Port3_NativeBatchBody.Ops) {X : Type}
 (D : aspis_core.digest.Digest32 X) (hash : X)
 (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot pos : Usize)
 (keys : Array U64 16#usize) (s : reference.Scratch)
 (key : U64) (view : Slice U8) (leaf : Array U8 32#usize)
 (more : pos<n) (room : s.n.val<16)
 (keyRead : Array.index_usize keys pos=ok key)
 (viewRead : base.op2 proof (Port4B_NativeLeaf.openingIndex lo key)=ok view)
 (leafRead : base.op6 D hash tree view=ok leaf) :
 NKV_FRef.verifier.candidate.batch_tree_loop.body
   (Port3_BatchStd.install base) D proof root tree hash lo n slot keys s.idx s.val s.n pos=
 (do let out ← reference.leaf_step s (Port4B_NativeLeaf.decodedIndex key) leaf
     ok (project s (Usize.wrapping_add pos 1#usize) out)) := by
 rw [←NKV_ActiveStep.source _ D proof root tree hash lo n slot keys s.idx s.val s.n pos more,
   Port4B_NativeLeaf.step base D hash proof root tree lo n slot pos keys s key view leaf
     more room keyRead viewRead leafRead,map_bind]
 congr 1
 funext out
 rw [map_ok,project_source]

set_option pp.proofs false
#print source
#print axioms project_source
#print axioms source
end NKV_LeafStep
end
