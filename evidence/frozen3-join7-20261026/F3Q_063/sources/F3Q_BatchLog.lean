import Port4B_BatchJoin
import F3Q_TreeLog
import F3Q_BatchCodeLog

set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BatchLog
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

def initial : reference.Scratch :=
  ⟨Array.repeat 16#usize 0#u32,Array.repeat 16#usize (Array.repeat 32#usize 0#u8),0#usize,0#usize⟩

/-- Accepted native batch0 OR batch1, with SAME physical Prepared/root/query
and three ordered scratch returns. PackedKeys and root/wire provenance are
explicit remaining LOCAL gates; this does not declare their concrete instances. -/
theorem accepted {X : Type}
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
    (keys : ∀ k : Fin 3, Port4B_TreeJoin.PackedKeys Port4B_Install.leaves p.queries q batch (Usize.ofNat k.val (by scalar_tac)))
    (root0 : Port3_BatchStage.root0 p=encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 p=encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded=encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (run : Port3_BatchStage.batch (Port4B_VerifyInstall.install Port4B_Install.leaves) D proof p folded batch hash=ok (.Ok ())) :
    ∃ log, eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q nodes batch.val Port4B_BatchJoin.initial)=
      (log,true) ∧
      (eval H (SdkC_Oracle.program (Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D)
        hash proof p folded batch))).1=log := by
  obtain ⟨idx1,idx2,idx3,val1,val2,val3,c0,c1,c2⟩ := Port3_BatchStage.accepted_slot_calls
    (Port4B_VerifyInstall.install Port4B_Install.leaves) D proof p folded batch hash run
  obtain ⟨a0,s0,h0,i0,v0,log0⟩ := F3Q_TreeLog.accepted (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 0#usize hb (by decide)
    (keys 0) (Port3_BatchStage.root0 p) root0 (nodes batch.val 0) (views _ _ hb (by decide))
    Port4B_BatchJoin.initial idx1 val1 c0
  have call1 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install Port4B_Install.leaves))
      (VTop_Checkpoint.digest D) proof p.queries (Port3_BatchStage.root1 p) batch 1#usize s0.idx s0.val hash=
        ok (.Ok (),idx2,val2) := by simpa only [i0,v0] using c1
  obtain ⟨a1,s1,h1,i1,v1,log1⟩ := F3Q_TreeLog.accepted (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 1#usize hb (by decide)
    (keys 1) (Port3_BatchStage.root1 p) root1 (nodes batch.val 1) (views _ _ hb (by decide))
    s0 idx2 val2 call1
  have call2 : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install Port4B_Install.leaves))
      (VTop_Checkpoint.digest D) proof p.queries folded batch 2#usize s1.idx s1.val hash=
        ok (.Ok (),idx3,val3) := by simpa only [i1,v1] using c2
  obtain ⟨a2,s2,h2,i2,v2,log2⟩ := F3Q_TreeLog.accepted (VTop_Checkpoint.digest D) hash H
    binary occupied sibling leaf p6 proof len parsed wire p.queries q batch 2#usize hb (by decide)
    (keys 2) folded root2 (nodes batch.val 2) (views _ _ hb (by decide)) s1 idx3 val3 call2
  refine ⟨_,Port4B_BatchJoin.compose H occupied sibling leaf parsed q nodes batch.val s0 s1 s2 _ _ _ h0 h1 h2,?_⟩
  have ordered := F3Q_BatchCodeLog.compose (VTop_Checkpoint.digest D) hash H p6.oracle proof p folded batch
    idx1 idx2 idx3 val1 val2 val3 c0 c1 c2
  have step0 := log0.trans (congrArg Prod.fst h0)
  have step1 := log1.trans (congrArg Prod.fst h1)
  have step2 := log2.trans (congrArg Prod.fst h2)
  simp only [i0,v0] at step1
  simp only [i1,v1] at step2
  exact ordered.trans (congrArg₂ List.append (congrArg₂ List.append step0 step1) step2)

#print axioms accepted
end AspisR1.F3Q_BatchLog
end
