import SdkC_BatchPair
import Op5T_SelectedPaths
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Authentication
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open MultiproofConeCanonical MultiproofConeP6Frozen2Stage

/-- The ideal source interpreter erases to its reply-driven digest instance. -/
theorem ideal_value {A Hash : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State)
    (law : ∀ parts, D.digest hash parts = .ok (encodeState (H (flatten parts))))
    (code : SdkC_Source.Code A) :
    (eval H (SdkC_Oracle.program code)).2 = CheckpointBytes5Effect.erase D hash code := by
  induction code with
  | done a => rfl
  | step r next ih =>
    cases r <;> simp only [SdkC_Oracle.program,eval,CheckpointBytes5Effect.erase,
      bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
  | read parts next ih =>
    simp only [SdkC_Oracle.program,eval,CheckpointBytes5Effect.erase,law,bind_tc_ok,ih]

def idealStage (H : Bytes → State) : VTop_Stages.aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst := {cloneInst := {clone := fun q => ok q}},
    digest := fun _ parts => .ok (encodeState (H (flatten parts)))}

/-- Native accepted source transports to the ideal batch on the SAME physical
proof, Prepared, root and batch. Native syscall totality is not a premise. -/
theorem stage_acceptance (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (accepted : Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () = .ok (.Ok ())) :
    Op5T_Install.stageBatch Port4B_Install.leaves (idealStage H) proof p root 1#usize () = .ok (.Ok ()) := by
  have real := (SdkC_BatchSource.stage_source hashv D source proof p root []).trans accepted
  have transported := (SdkC_Oracle.accepted_transport hashv sha256 H p1 syscall
    (SdkC_BatchSource.stageCode hashv proof p root) [] (.Ok ()) real).1
  have ideal := ideal_value (VTop_Checkpoint.digest (idealStage H)) () H (fun _ => rfl)
    (SdkC_BatchSource.stageCode hashv proof p root)
  have erased : CheckpointBytes5Effect.erase (VTop_Checkpoint.digest (idealStage H)) ()
      (SdkC_BatchSource.stageCode hashv proof p root) =
      Op5T_Install.stageBatch Port4B_Install.leaves (idealStage H) proof p root 1#usize () := by
    simp only [SdkC_BatchSource.stageCode,SdkC_BatchSource.map_erasure,SdkC_BatchSource.erasure]
    rfl
  exact erased.symm.trans (ideal.symm.trans transported)

/-- Actual accepted partial-syscall source authenticates every batch1 index.
The read conclusion refers explicitly to canonical P6; containment in the
whole SDK source log is still a separate, unproved composition obligation. -/
theorem stage_paths (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (len : proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val)
    (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
    (q : Fin 22 → Fin 262144) (queries : Port4B_KeyInstall.queries p.queries = q)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val = OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (root0 : Port3_BatchStage.root0 p = encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 p = encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded = encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (accepted : Op5T_Install.stageBatch Port4B_Install.leaves D proof p folded 1#usize () = .ok (.Ok ())) :
    ∀ kind, kind < 3 → ∀ pos, pos ∈ OraclePortSelectedDraft.batchPositions 1 →
      ∃ path : BinMerkle32Path.Path (BinMultiproof.slots 18 (OraclePortSelectedDraft.index q kind pos)),
        BinMerkle32Path.foldPath H path (H (OraclePortSelectedDraft.leaf parsed kind pos)) =
          OraclePortBatchDraft.committedRoot parsed kind ∧
        ∀ a ∈ BinMerkle32Leaf.fullTrace H path (OraclePortSelectedDraft.leaf parsed kind pos),
          Read (eval H (sourceBatch Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf
            parsed q nodes 1 Port4B_BatchJoin.initial)).1 a := by
  exact Op5T_SelectedPaths.indexed_paths (idealStage H) () H (fun _ => rfl)
    proof len parsed wire p folded q queries 1#usize (by decide) nodes views root0 root1 root2
    (stage_acceptance hashv D source sha256 H p1 syscall proof p folded accepted)

#print axioms ideal_value
#print axioms stage_acceptance
#print axioms stage_paths
end AspisR1.SdkC_Authentication
end
