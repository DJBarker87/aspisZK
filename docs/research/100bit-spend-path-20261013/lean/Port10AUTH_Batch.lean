import Port10AUTH_BatchLog

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Batch
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical
/-- Accepted native batch0 OR batch1, with SAME physical Prepared/root/query
and three ordered scratch returns. PackedKeys and root/wire provenance are
explicit remaining LOCAL gates; this does not declare their concrete instances. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest D) hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
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
    eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes batch.val Port4B_BatchJoin.initial)=
      (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash
        (Port9OR_Batch.code base (VTop_Checkpoint.digest D) hash proof p folded batch)).1,true) := by
  obtain ⟨idx1,idx2,idx3,val1,val2,val3,c0,c1,c2⟩ := Port3_BatchStage.accepted_slot_calls
    (Port4B_VerifyInstall.install base) D proof p folded batch hash run
  obtain ⟨s0,h0,i0,v0⟩ := Port10AUTH_Tree.accepted base (VTop_Checkpoint.digest D) hash H
    oracle occupied sibling leaf occupiedGate siblingGate leafGate proof len parsed wire p.queries q batch 0#usize hb (by decide)
    (keys 0) (Port3_BatchStage.root0 p) root0 (nodes batch.val 0) (views _ _ hb (by decide))
    Port4B_BatchJoin.initial idx1 val1 c0
  have call1 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install base))
      (VTop_Checkpoint.digest D) proof p.queries (Port3_BatchStage.root1 p) batch 1#usize s0.idx s0.val hash=
        ok (.Ok (),idx2,val2) := by simpa only [i0,v0] using c1
  obtain ⟨s1,h1,i1,v1⟩ := Port10AUTH_Tree.accepted base (VTop_Checkpoint.digest D) hash H
    oracle occupied sibling leaf occupiedGate siblingGate leafGate proof len parsed wire p.queries q batch 1#usize hb (by decide)
    (keys 1) (Port3_BatchStage.root1 p) root1 (nodes batch.val 1) (views _ _ hb (by decide))
    s0 idx2 val2 call1
  have call2 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install base))
      (VTop_Checkpoint.digest D) proof p.queries folded batch 2#usize s1.idx s1.val hash=
        ok (.Ok (),idx3,val3) := by simpa only [i1,v1] using c2
  obtain ⟨s2,h2,i2,v2⟩ := Port10AUTH_Tree.accepted base (VTop_Checkpoint.digest D) hash H
    oracle occupied sibling leaf occupiedGate siblingGate leafGate proof len parsed wire p.queries q batch 2#usize hb (by decide)
    (keys 2) folded root2 (nodes batch.val 2) (views _ _ hb (by decide)) s1 idx3 val3 call2
  have code0 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root0 p) batch 0#usize Port4B_BatchJoin.initial.idx Port4B_BatchJoin.initial.val).trans c0
  have code1 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx1 val1).trans c1
  have code2 := (Port9OR_BatchTree.source base (VTop_Checkpoint.digest D) (VTop_Checkpoint.digest D) hash
    proof p.queries folded batch 2#usize idx2 val2).trans c2
  have log1 := congrArg₂ (fun idx val => Port9OR_BatchTree.code base (VTop_Checkpoint.digest D) hash
    proof p.queries (Port3_BatchStage.root1 p) batch 1#usize idx val) i0 v0
  have log2 := congrArg₂ (fun idx val => Port9OR_BatchTree.code base (VTop_Checkpoint.digest D) hash
    proof p.queries folded batch 2#usize idx val) i1 v1
  have h1' := h1.trans (congrArg (fun code =>
    (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash code).1,(true,s1))) log1)
  have h2' := h2.trans (congrArg (fun code =>
    (CheckpointBytes5Inputs.observe (Port9OR_Code.trace (VTop_Checkpoint.digest D) hash code).1,(true,s2))) log2)
  have combined := Port4B_BatchJoin.compose H occupied sibling leaf parsed q nodes batch.val s0 s1 s2 _ _ _ h0 h1' h2'
  have logs := Port10AUTH_BatchLog.logs base (VTop_Checkpoint.digest D) hash proof p folded batch idx1 idx2 idx3 val1 val2 val3
    code0 code1 code2
  have observed := congrArg CheckpointBytes5Inputs.observe logs
  simp only [CheckpointBytes5Inputs.observe,List.map_append] at observed
  exact combined.trans (congrArg (fun log => (log,true)) observed.symm)

#print axioms accepted
end AspisR1.Port10AUTH_Batch
end
