import RPz7_SdkD_NodeViews
import RPz7_SdkD_PhysicalRoots
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_FirstPaths
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
    (proof : Slice U8) (len : proof.val.length = 57607)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (p : AspisR1CurrentCaller.verifier.Prepared)
    (input scratch : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (prepareCall : AspisR1CurrentCaller.verifier.candidate.prepare
      (RowShape_InstalledSlots.verifierOps ops B std) D semantic proof () none input = ok (.Ok p,scratch))
    (root : Array U8 32#usize) (view : Slice U8)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize} = ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view = ok (.Ok root))
    (stored : Bytes) (parsed : OraclePortCompactDraft.Parsed)
    (parser : OraclePortCompactDraft.parse stored = some parsed) (wire : parsed.wire = bytesOf proof.val)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E) (rho : OraclePortCheckpointAbiC5.K)
    (q : Fin 22 → Fin 262144)
    (prepare : Port5Q1_QueryPorts.SessionAPrepare (Tx1Q_Carriers.prepared p) data q rho)
    (accepted : Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize () = ok (.Ok ())) :
    ∀ kind, kind < 3 → ∀ pos, pos ∈ OraclePortSelectedDraft.batchPositions 0 →
      ∃ path : BinMerkle32Path.Path (BinMultiproof.slots 18 (OraclePortSelectedDraft.index q kind pos)),
        BinMerkle32Path.foldPath H path (H (OraclePortSelectedDraft.leaf parsed kind pos)) =
          OraclePortBatchDraft.committedRoot parsed kind ∧
        ∀ a ∈ BinMerkle32Leaf.fullTrace H path (OraclePortSelectedDraft.leaf parsed kind pos),
          Read (eval H (sourceBatch Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf
            parsed q (SdkD_NodeViews.nodes proof) 0 Port4B_BatchJoin.initial)).1 a := by
  obtain ⟨r0,r1,roots,physical0,physical1⟩ :=
    SdkD_PhysicalRoots.prepared ops B std D semantic proof () p input scratch prepareCall
  have boundRoots := SdkD_RootBinding.current proof p stored parsed parser wire r0 r1 roots physical0 physical1
  have folded := Port4B_FoldedCut.model proof view root len parsed wire range copy
  have root2 := Port4B_Prepared.digest_of_bytes root _ folded
  exact SdkC_FirstAuthentication.current_paths hashv D source sha256 H p1 syscall proof len parsed wire p
    (Tx1Q_Carriers.prepared p) root q (SdkD_QueryBinding.current p data q rho prepare)
    (SdkD_NodeViews.nodes proof) (fun b k _ _ => SdkD_NodeViews.views proof parsed wire b k)
    boundRoots.1 boundRoots.2 root2 accepted

#print axioms indexed
end AspisR1.SdkD_FirstPaths
end
