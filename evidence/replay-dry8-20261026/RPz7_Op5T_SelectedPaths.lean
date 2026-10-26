import RPz7_Op5T_NativeAuth
import OraclePortFrozenOrderSelectedRecovery
set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5T_SelectedPaths
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeRef MultiproofConePhysicalDigest MultiproofConePhysicalTransport MultiproofConeCanonical
open MultiproofConeP6Batch MultiproofConeP6Frozen2Stage

/-- Every selected opening has an authentication path at its EXACT queried
index, with all path reads present in the body's canonical P6 log. Equal roots
alone are never used as a substitute for this indexed conclusion. -/
theorem indexed_paths {Hash : Type} (D : VTop_Stages.aspis_core.digest.Digest32 Hash)
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
    ∀ kind, kind < 3 → ∀ pos, pos ∈ OraclePortSelectedDraft.batchPositions batch.val →
      ∃ path : BinMerkle32Path.Path (BinMultiproof.slots 18 (OraclePortSelectedDraft.index q kind pos)),
        BinMerkle32Path.foldPath H path (H (OraclePortSelectedDraft.leaf parsed kind pos)) =
          OraclePortBatchDraft.committedRoot parsed kind ∧
        ∀ a ∈ BinMerkle32Leaf.fullTrace H path (OraclePortSelectedDraft.leaf parsed kind pos),
          Read (eval H (sourceBatch Op5T_P6.parent Op5T_P6.parent referenceLeaf parsed q nodes batch.val
            Port4B_BatchJoin.initial)).1 a := by
  obtain ⟨log,run,frozen⟩ := Op5T_NativeAuth.accepted_batch D hash H oracle proof len parsed wire p folded q
    queries batch hb nodes views root0 root1 root2 success
  have accepted : (eval H (OraclePortFrozen2.batch parsed q
      [(batch.val,0),(batch.val,1),(batch.val,2)])).2 = true := by rw [frozen]
  intro kind hk pos hp
  have member : (batch.val,kind) ∈ [(batch.val,0),(batch.val,1),(batch.val,2)] := by
    interval_cases kind <;> simp
  have slotOK := OraclePortFrozenOrder.slots_accepted H parsed q _ accepted (batch.val,kind) member
  obtain ⟨path,root,reads⟩ := OraclePortFrozenOrder.slot_path H parsed q batch.val kind pos hp slotOK
  refine ⟨path,root,?_⟩
  intro a ha
  have read := OraclePortFrozenOrder.slots_read H parsed q _ accepted (batch.val,kind) member a (reads a ha)
  rw [frozen] at read
  rw [run]
  exact read

#print axioms indexed_paths
end AspisR1.Op5T_SelectedPaths
end
