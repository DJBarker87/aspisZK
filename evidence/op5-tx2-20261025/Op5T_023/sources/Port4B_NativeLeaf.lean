import Port4B_LeafStep

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_NativeLeaf
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
open Port3_NativeBatchCalls (Indices Values)
open Port4B_LeafStep MultiproofConeRef

def decodedIndex (key : U64) : U32 := UScalar.cast .U32 (U64.wrapping_shr key 8#u32)
def openingIndex (lo : Usize) (key : U64) : Usize :=
  Usize.wrapping_add lo (UScalar.cast .Usize (key &&& 255#u64))

/-- Exact current native prefix, followed by the proved post-hash control. -/
theorem active (leaves : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot d pos : Usize)
    (keys : Array U64 16#usize) (idx : Indices) (val : Values) (more : pos<n) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root tree hash lo n slot keys idx val d pos =
      (do let key ← Array.index_usize keys pos
          let view ← leaves.op2 proof (openingIndex lo key)
          let leaf ← leaves.op6 D hash tree view
          post idx val d (decodedIndex key) leaf (Usize.wrapping_add pos 1#usize)) := by
  unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
  rw [if_pos more]
  rfl

/-- Native dedup/write uses the actual just-returned digest. Each premise is
one local key/opening/hash read, rather than a successful slot or loop. -/
theorem step (leaves : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (proof : Slice U8) (root : Array U8 32#usize) (tree lo n slot pos : Usize)
    (keys : Array U64 16#usize) (s : reference.Scratch)
    (key : U64) (view : Slice U8) (leaf : Array U8 32#usize)
    (more : pos<n) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok key)
    (viewRead : leaves.op2 proof (openingIndex lo key)=ok view)
    (leafRead : leaves.op6 D hash tree view=ok leaf) :
    Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install leaves) D proof root tree hash lo n slot keys s.idx s.val s.n pos =
      (do let out ← reference.leaf_step s (decodedIndex key) leaf
          ok (project s (Usize.wrapping_add pos 1#usize) out)) := by
  rw [active leaves D hash proof root tree lo n slot s.n pos keys s.idx s.val more]
  simp only [keyRead,viewRead,leafRead,bind_tc_ok]
  exact reference_post s (decodedIndex key) leaf (Usize.wrapping_add pos 1#usize) room

#print axioms active
#print axioms step
end AspisR1.Port4B_NativeLeaf
end
