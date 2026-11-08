import NNU_MerkleChildren
import NKV_KeyInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleKeys
open Aeneas Aeneas.Std Result VTop_Stages

theorem source (env : RSL.Env) (pub proof ck : Slice U8)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resume : NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
  ck proof pub .S2 ()=.ok (.Ok (p,a)))
 (tree : Usize) (bound : tree.val < 3) :
 ∃ sorted,
 (do let keys ← (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op4 p.queries 10#usize 12#usize tree
     (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op5 keys 12#usize)=.ok sorted ∧
 (do let keys ← Port4B_Install.leaves.op4 p.queries 10#usize 12#usize tree
     Port4B_Install.leaves.op5 keys 12#usize)=.ok sorted ∧
 Port4B_LeafLoop.KeyStream (Port4B_KeyInstall.queries p.queries) 1 tree.val sorted 0#usize
   (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries p.queries) 1 tree.val) := by
 have canonical := NNU_MerkleSlots.same_resume env pub proof ck p a resume
 obtain ⟨sorted,run,span,stream⟩ := NKV_KeyInvocation.source (LIBB_PartitionEnv.H env)
   p.queries 1 tree (by decide) bound canonical
 have literal : (do
   let keys ← (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op4 p.queries 10#usize 12#usize tree
   (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env)).op5 keys 12#usize)=.ok sorted := run
 refine ⟨sorted,literal,?_,stream⟩
 change (do let keys ← Port4B_KeyInstall.build p.queries 10#usize 12#usize tree
            MultiproofSortRef.sort_reference.sort_rows keys 1#usize 12#usize)=.ok sorted
 change (do let keys ← NJS_Extract.verifier.candidate.batch_keys p.queries 10#usize 12#usize tree
            NJS_Extract.verifier.candidate.sort_batch_keys keys 12#usize)=.ok sorted at literal
 rw [NNU_MerkleChildren.key p.queries tree bound canonical] at literal
 simp only [NNU_MerkleChildren.sort] at literal
 exact literal
#print axioms source
end AspisR1.NNU_MerkleKeys
end
