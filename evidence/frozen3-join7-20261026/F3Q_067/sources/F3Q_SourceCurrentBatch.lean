import F3Q_BatchNative
import F3Q_BatchSyntax
import SdkC_FirstAuthentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_SourceCurrentBatch
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open MultiproofConeCanonical
theorem current (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts,D.digest () parts=hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof : Slice U8) (len : proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val)
    (p : AspisR1CurrentCaller.verifier.Prepared) (folded : Array U8 32#usize)
    (q : Fin 22 → Fin 262144) (queries : Port4B_KeyInstall.queries p.queries = q)
    (nodes : Nat → Nat → Slice U8)
    (views : ∀ b k, b<2 → k<3 → bytesOf (nodes b k).val = OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*b+k)) (32*OraclePortSelectedDraft.capacity (3*b+k)))
    (root0 : Port3_BatchStage.root0 (Tx1Q_Carriers.prepared p) = encodeState (OraclePortBatchDraft.committedRoot parsed 0))
    (root1 : Port3_BatchStage.root1 (Tx1Q_Carriers.prepared p) = encodeState (OraclePortBatchDraft.committedRoot parsed 1))
    (root2 : folded = encodeState (OraclePortBatchDraft.committedRoot parsed 2))
    (success : Op5T_Install.currentBatch Port4B_Install.leaves D proof p folded 0#usize ()=ok (.Ok ())) :
    SdkC_Source.readLog (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p folded) []).2=
      (eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch0)).1 ∧
    (eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch0)).2=true := by
  have real := (SdkC_BatchSource.current_source hashv D source proof p folded []).trans success
  have observed := (congrArg Prod.fst (SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
    (SdkC_BatchSource.currentCode hashv proof p folded) (.Ok ()) real)).symm
  have native := SdkC_FirstAuthentication.current_acceptance hashv D source sha256 H p1 syscall proof p (Tx1Q_Carriers.prepared p) folded success
  obtain ⟨log,run,frozen,ordered⟩ := F3Q_BatchNative.accepted_batch (SdkC_Authentication.idealStage H) () H
    (fun _=>rfl) proof len parsed wire (SdkC_FirstAuthentication.staged (Tx1Q_Carriers.prepared p) p) folded q queries 0#usize (by decide) nodes views root0 root1 root2 native
  have syntax := F3Q_BatchSyntax.current hashv (VTop_Checkpoint.digest (SdkC_Authentication.idealStage H)) H proof p folded
  exact ⟨observed.trans (syntax.trans (ordered.trans (congrArg Prod.fst frozen).symm)),congrArg Prod.snd frozen⟩

#print axioms current
end AspisR1.F3Q_SourceCurrentBatch
end
