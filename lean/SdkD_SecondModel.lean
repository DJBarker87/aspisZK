import SdkD_FirstPaths
import SdkD_CheckpointBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_SecondModel
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open MultiproofConeCanonical MultiproofConeP6Frozen2Stage

/-- Root and node-view provenance is DERIVED from the actual preparation and
folded-root copy. Only Session A's named query/field preparation law remains. -/
theorem indexed (ops : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (proof proof1 pub0 pub1 checkpoint : Slice U8) (len : proof.val.length = 57607)
    (len1 : proof1.val.length = 57607) (savedVec : alloc.vec.Vec U8) (reserved : Bool)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (p : AspisR1CurrentCaller.verifier.Prepared)
    (p2 : AspisR1Stage2.verifier.Prepared) (a0 a2 : AspisR1Stage2.verifier.Accumulator)
    (input scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (prepareCall : AspisR1CurrentCaller.verifier.candidate.prepare
      (RowShape_InstalledSlots.verifierOps ops B std) D semantic proof () none input = ok (.Ok p,scratch))
    (root : Array U8 32#usize) (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof1 {start:=7751#usize,«end»:=7783#usize} = ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root))
    (stored : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse stored = some parsed) (wire : parsed.wire = bytesOf proof.val)
    (wire1 : parsed.wire = bytesOf proof1.val)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (q : Fin 22 → Fin 262144)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared p) data q rho)
    (write : Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (Tx1Q_Carriers.prepared p)
      a0 proof pub0 () = ok savedVec)
    (same : bytesOf checkpoint.val = bytesOf savedVec.val)
    (read : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
      (VTop_Checkpoint.digest (Tx1Q_Install.digest D)) checkpoint proof1 pub1 .S2 () = ok (.Ok (p2,a2)))
    (accepted : Op5T_Install.stageBatch Port4B_Install.leaves (Tx1Q_Install.digest D)
      proof1 p2 root 1#usize () = ok (.Ok ())) :
    (eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch1)).2 = true := by
  obtain ⟨r0,r1,roots,physical0,physical1⟩ :=
    SdkD_PhysicalRoots.prepared ops B std D semantic proof () p input scratch prepareCall
  have boundRoots := SdkD_RootBinding.current proof p stored parsed parser wire r0 r1 roots physical0 physical1
  have folded := Port4B_FoldedCut.model proof1 view root len1 parsed wire1 range copy
  have root2 := Port4B_Prepared.digest_of_bytes root _ folded
  have fields := SdkD_CheckpointBinding.fields reserved (Tx1Q_Install.digest D)
    (Tx1Q_Carriers.prepared p) p2 a0 a2 checkpoint proof pub0 proof1 pub1 () savedVec write same read
  have queries : Port4B_KeyInstall.queries p2.queries = q := by
    rw [fields.2.2]
    exact SdkD_QueryBinding.current p data q rho prepare
  have native := SdkC_Authentication.stage_acceptance hashv (Tx1Q_Install.digest D)
    (fun parts => source parts) sha256 H p1 syscall proof1 p2 root accepted
  obtain ⟨log,run,frozen⟩ := Op5T_NativeAuth.accepted_batch (SdkC_Authentication.idealStage H) () H
    (fun _ => rfl) proof1 len1 parsed wire1 p2 root q queries 1#usize (by decide)
    (SdkD_NodeViews.nodes proof1) (fun b k _ _ => SdkD_NodeViews.views proof1 parsed wire1 b k)
    (fields.1.trans boundRoots.1) (fields.2.1.trans boundRoots.2) root2 native
  exact congrArg Prod.snd frozen

#print axioms indexed
end AspisR1.SdkD_SecondModel
end
