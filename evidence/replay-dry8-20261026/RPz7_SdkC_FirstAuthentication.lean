import RPz7_SdkC_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_FirstAuthentication
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open MultiproofConeCanonical MultiproofConeP6Frozen2Stage

/-- Only fields consumed by batch are transported. Every other field of seed
is ignored by this helper; no equality of whole Prepared carriers is asserted. -/
def staged (seed : VTop_Stages.verifier.Prepared) (p : AspisR1CurrentCaller.verifier.Prepared) :
    VTop_Stages.verifier.Prepared := {seed with queries := p.queries, roots := p.roots}

theorem current_acceptance (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (seed : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (accepted : Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () = .ok (.Ok ())) :
    Op5T_Install.stageBatch Port4B_Install.leaves (SdkC_Authentication.idealStage H)
      proof (staged seed p) root 0#usize () = .ok (.Ok ()) := by
  have real := (SdkC_BatchSource.current_source hashv D source proof p root []).trans accepted
  have transported := (SdkC_Oracle.accepted_transport hashv sha256 H p1 syscall
    (SdkC_BatchSource.currentCode hashv proof p root) [] (.Ok ()) real).1
  let E := VTop_Checkpoint.digest (SdkC_Authentication.idealStage H)
  have ideal := SdkC_Authentication.ideal_value E () H (fun _ => rfl)
    (SdkC_BatchSource.currentCode hashv proof p root)
  have returned := ideal.symm.trans transported
  simp only [SdkC_BatchSource.currentCode,SdkC_BatchSource.map_erasure,SdkC_BatchSource.erasure] at returned
  have raw := (Op5T_Install.map_success_iff Op5T_Install.currentError _).mp returned
  change Op5T_Install.mapResult Op5T_Install.stageError
    (Op5T_Install.body Port4B_Install.leaves E proof p.queries p.roots root 0#usize ()) = _
  exact (Op5T_Install.map_success_iff Op5T_Install.stageError _).mpr raw

/-- All batch0 indices under the actual partial syscall interpretation, with
exact original Prepared query/root arrays and explicit model read carrier. -/
theorem current_paths (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (len : proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val)
    (p : AspisR1CurrentCaller.verifier.Prepared) (seed : VTop_Stages.verifier.Prepared)
    (folded : Array U8 32#usize)
    (q : Fin 22 → Fin 262144) (queries : Port4B_KeyInstall.queries p.queries = q)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val = OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (root0 : Port3_BatchStage.root0 (staged seed p) = encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 (staged seed p) = encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded = encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (accepted : Op5T_Install.currentBatch Port4B_Install.leaves D proof p folded 0#usize () = .ok (.Ok ())) :
    ∀ kind, kind < 3 → ∀ pos, pos ∈ OraclePortSelectedDraft.batchPositions 0 →
      ∃ path : BinMerkle32Path.Path (BinMultiproof.slots 18 (OraclePortSelectedDraft.index q kind pos)),
        BinMerkle32Path.foldPath H path (H (OraclePortSelectedDraft.leaf parsed kind pos)) =
          OraclePortBatchDraft.committedRoot parsed kind ∧
        ∀ a ∈ BinMerkle32Leaf.fullTrace H path (OraclePortSelectedDraft.leaf parsed kind pos),
          Read (eval H (sourceBatch Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf
            parsed q nodes 0 Port4B_BatchJoin.initial)).1 a := by
  exact Op5T_SelectedPaths.indexed_paths (SdkC_Authentication.idealStage H) () H (fun _ => rfl)
    proof len parsed wire (staged seed p) folded q queries 0#usize (by decide) nodes views root0 root1 root2
    (current_acceptance hashv D source sha256 H p1 syscall proof p seed folded accepted)

#print axioms current_acceptance
#print axioms current_paths
end AspisR1.SdkC_FirstAuthentication
end
