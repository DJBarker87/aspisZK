import Port4B_TreeJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_BatchJoin
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

def initial : reference.Scratch :=
  ⟨Array.repeat 16#usize 0#u32,Array.repeat 16#usize (Array.repeat 32#usize 0#u8),0#usize,0#usize⟩

/-- Fixed three-slot source composition retains the exact chronological
scratch and logs; it never assumes successful whole-batch agreement. -/
theorem compose (H : Bytes → State) (occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf) (parsed : OraclePortCompactDraft.Parsed)
    (q : Fin 22 → Fin 262144) (nodes : Nat → Nat → Slice U8) (batch : Nat)
    (s0 s1 s2 : reference.Scratch) (l0 l1 l2 : List (Bytes × State))
    (h0 : eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
      parsed q batch 0 (nodes batch 0) initial)=(l0,(true,s0)))
    (h1 : eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
      parsed q batch 1 (nodes batch 1) s0)=(l1,(true,s1)))
    (h2 : eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
      parsed q batch 2 (nodes batch 2) s1)=(l2,(true,s2))) :
    eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes batch initial)=
      (l0++l1++l2,true) := by
  simp only [MultiproofConeP6Frozen2Stage.sourceBatch,MultiproofConeP6Frozen2Stage.sequence,eval_bind,
    h0,h1,h2,if_true,eval,List.append_nil,List.append_assoc]

/-- Accepted native batch0 OR batch1, with SAME physical Prepared/root/query
and three ordered scratch returns. PackedKeys and root/wire provenance are
explicit remaining LOCAL gates; this does not declare their concrete instances. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)) hash H
      binary occupied sibling leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
    (q : Fin 22 → Fin 262144) (batch : Usize) (hb : batch.val<2)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val=OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (keys : ∀ k : Fin 3, Port4B_TreeJoin.PackedKeys base p.queries q batch (Usize.ofNat k.val (by scalar_tac)))
    (root0 : Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded=encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (run : Port3_BatchStage.batch (Port4B_VerifyInstall.install base) D proof p folded batch hash=ok (.Ok ())) :
    ∃ log, eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes batch.val initial)=
      (log,true) := by
  obtain ⟨idx1,idx2,idx3,val1,val2,val3,c0,c1,c2⟩ := Port3_BatchStage.accepted_slot_calls
    (Port4B_VerifyInstall.install base) D proof p folded batch hash run
  obtain ⟨a0,s0,h0,i0,v0⟩ := Port4B_TreeJoin.accepted base (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 0#usize hb (by decide)
    (keys 0) (Port3_BatchStage.root0 p) root0 (nodes batch.val 0) (views _ _ hb (by decide))
    initial idx1 val1 c0
  have call1 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install base))
      (VTop_Checkpoint.digest D) proof p.queries (Port3_BatchStage.root1 p) batch 1#usize s0.idx s0.val hash=
        ok (.Ok (),idx2,val2) := by simpa only [i0,v0] using c1
  obtain ⟨a1,s1,h1,i1,v1⟩ := Port4B_TreeJoin.accepted base (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 1#usize hb (by decide)
    (keys 1) (Port3_BatchStage.root1 p) root1 (nodes batch.val 1) (views _ _ hb (by decide))
    s0 idx2 val2 call1
  have call2 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install base))
      (VTop_Checkpoint.digest D) proof p.queries folded batch 2#usize s1.idx s1.val hash=
        ok (.Ok (),idx3,val3) := by simpa only [i1,v1] using c2
  obtain ⟨a2,s2,h2,i2,v2⟩ := Port4B_TreeJoin.accepted base (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 2#usize hb (by decide)
    (keys 2) folded root2 (nodes batch.val 2) (views _ _ hb (by decide)) s1 idx3 val3 call2
  exact ⟨_,compose H occupied sibling leaf parsed q nodes batch.val s0 s1 s2 _ _ _ h0 h1 h2⟩

#print axioms compose
#print axioms accepted
end AspisR1.Port4B_BatchJoin
end
