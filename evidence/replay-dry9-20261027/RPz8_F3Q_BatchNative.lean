import F3Q_BatchLog
import RPz7_Op5T_P6
import OraclePortFrozenOrderSelectedRecovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_BatchNative
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeRef MultiproofConePhysicalDigest MultiproofConePhysicalTransport MultiproofConeCanonical
open MultiproofConeP6Batch MultiproofConeP6Frozen2Stage

/-- Native concrete parent acceptance supplies the canonical P6 execution.
Packed-key/callback/leaf gates are discharged. Remaining source provenance
is explicit: physical wire/queries/roots and the primitive hash law. This
is a local source theorem; it does not bind an arbitrary SDK child log. -/
theorem accepted_batch {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (rawOracle H input))
    (proof : Slice U8) (len : proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val)
    (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
    (q : Fin 22 → Fin 262144) (queries : Port4B_KeyInstall.queries p.queries = q)
    (batch : Usize) (hb : batch.val < 2) (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val = OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (root0 : Port3_BatchStage.root0 p = encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 p = encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded = encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (success : Op5T_Install.stageBatch Port4B_Install.leaves D proof p folded batch hash = ok (.Ok ())) :
    ∃ log,
      eval H (sourceBatch Op5T_P6.parent Op5T_P6.parent referenceLeaf parsed q nodes batch.val
        Port4B_BatchJoin.initial) = (log,true) ∧
      eval H (OraclePortFrozen2.batch parsed q [(batch.val,0),(batch.val,1),(batch.val,2)]) = (log,true) ∧
      (eval H (SdkC_Oracle.program (Port9OR_Batch.code Port4B_Install.leaves (VTop_Checkpoint.digest D)
        hash proof p folded batch))).1=log := by
  let digest := Port4B_VerifyInstall.digest (VTop_Checkpoint.digest D)
  have p6 := Op5T_P6.boundary digest hash H oracle
  have native : Port3_BatchStage.batch
      (Port4B_VerifyInstall.install (Port4B_KeyInstall.install Port4B_Install.leaves))
      D proof p folded batch hash = ok (.Ok ()) := by
    rw [Port4B_Install.parent]
    exact (Op5T_Concrete.stage_source D proof p folded batch hash).symm.trans success
  have keys : ∀ k : Fin 3, Port4B_TreeJoin.PackedKeys
      (Port4B_KeyInstall.install Port4B_Install.leaves) p.queries q batch
      (Usize.ofNat k.val (by scalar_tac)) := by
    intro k
    exact Port4B_KeyInstall.packed Port4B_Install.leaves p.queries q queries batch
      (Usize.ofNat k.val (by scalar_tac)) hb (by simpa using k.isLt)
  obtain ⟨log,run,ordered⟩ := F3Q_BatchLog.accepted
    D hash H Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent referenceLeaf p6
    proof len parsed wire p folded q batch hb nodes views keys root0 root1 root2 native
  have joined := sourceBatch_eq digest hash H Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent
    referenceLeaf p6 parsed q nodes views batch.val hb Port4B_BatchJoin.initial
  have accepted : (eval H (MultiproofConeFrozen2Stage.sourceBatch parsed q nodes batch.val
      Port4B_BatchJoin.initial)).2 = true := by rw [← joined,run]
  have frozen := MultiproofConeFrozen2Stage.accepted_batch digest hash H oracle parsed q nodes
    batch.val Port4B_BatchJoin.initial (fun k hk => views batch.val k hb hk) accepted
  exact ⟨log,run,frozen.symm.trans (joined.symm.trans run),ordered⟩

#print axioms accepted_batch
end AspisR1.F3Q_BatchNative
end
