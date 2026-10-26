import RPz7_Op5T_D189
import RPz7_SInt2_ClaimsUnrolledSdk
import S2W_D189Consolidation
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Op5T_Claims
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

open ClaimsUnrolledSdk
theorem accepted_pair_claims {W A E M Cv : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps adapterOps ops B claimsStd) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (port : ChildConeJoin E (sdkOps adapterOps ops B claimsStd)) (firstMarks : Op5T_Marks.FirstMarks port) (secondMarks : Op5T_Marks.SecondMarks port) :
    ∃ f s outer pre middle fs ss,
      SourceCuts (sdkOps adapterOps ops B claimsStd) e1.first (e2.second secondSizes) saved f s ∧
      S2W_ExpandedTrace.runExpanded (sdkOps adapterOps ops B claimsStd) (children port)
        (S2W_Observation.two (sdkOps adapterOps ops B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps adapterOps ops B claimsStd)
        (S2W_Observation.two (sdkOps adapterOps ops B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps adapterOps ops B claimsStd) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase ops (ClaimsUnrolledFinish.install claimsStd B)).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues
              AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install claimsStd B))
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic
                (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            v.semantic () none = ok (.Ok sem) ∧
          AspisR1PublicPreparation.PrefixAdapter.parseAccepted v.semantic = ok (.Ok claimsPrefix) ∧
          ClaimsUnrolledFinish.reference claimsStd claimsPrefix = ok (.Ok (retainedSem sem).claims)) ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin (sdkOps adapterOps ops B claimsStd) decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin (sdkOps adapterOps ops B claimsStd) decode H s.pub s.proof s.checkpoint →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps adapterOps ops B claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  have original := Op5T_D189.accepted_run L sdk copy std allocator
    e1 e2 w1 w2 admission1 admission2 (sdkOps adapterOps ops B claimsStd)
    native1 native2 hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
    port firstMarks secondMarks
  obtain ⟨f, s, outer, pre, middle, fs, ss, cuts, expanded, owned, layout,
    unchanged, before1, before2, caller⟩ := original
  have originalAccepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy
      allocator e1 program data1 state1 = ok (.Ok (saved,post1,final1)) := by
    rw [← AspisS6SdkFirstObjectEquivalence.first_eq_original]
    exact accepted1
  have sdkSource := candidate_sdk_selected_semantic_trace L sdk copy std allocator
    e1 w1 admission1 adapterOps ops B claimsStd native1 native2 hashv extraction
    p root length program data1 saved state1 final1 post1 originalAccepted
  obtain ⟨written, observed, steps⟩ := sdkSource
  obtain ⟨selectedPublic, publicSemantic, selectedCut, publicBytes, publicLength,
    payload, decoded, split, zero, semantic, y1, v, sem, prepared, scratch,
    viewCall, variant, semanticCall, prepareCall, powers, claimPowers, claim,
    numeric, challengesNumeric, seeds, meaning, eachPower, trace, queries,
    ⟨claimsPrefix, parsed, normalizedClaims⟩, tail⟩ := steps (e2.second secondSizes) f s cuts
  exact ⟨f, s, outer, pre, middle, fs, ss, cuts, expanded, owned, layout,
    unchanged, before1, before2,
    ⟨selectedPublic, publicSemantic, selectedCut, semantic, y1, v, sem, claimsPrefix,
      viewCall, semanticCall, parsed, normalizedClaims⟩, caller⟩

#print axioms accepted_pair_claims
end AspisR1.Op5T_Claims
end
