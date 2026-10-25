import Op5I_EventCounterexample

set_option autoImplicit false
noncomputable section
namespace AspisR1.Op5I_AcceptedCarrierCounterexample
open Aeneas Aeneas.Std Result
open Op5I_EventCounterexample
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

open S2W_Trace S2W_ExpandedTrace

/-- Select the child read records. Outer calls and scheduling marks are not
silently reinterpreted as hash replies. -/
def readEvents (trace : List (S2W_ExpandedTrace.Event ReadEvent)) : List ReadEvent :=
  trace.filterMap fun event => match event with
    | .child read => some read
    | _ => none

/-- Explicitly inconsistent reply; no oracle or cryptographic assumption. -/
def wrong (H : Bytes → State) : ReadEvent :=
  ([], if H [] = (fun _ => 0) then (fun _ => 1) else (fun _ => 0))

theorem wrong_reply (H : Bytes → State) : (wrong H).2 ≠ H (wrong H).1 := by
  unfold wrong
  dsimp only
  split
  · rename_i zero
    intro equal
    have atZero := congrFun (equal.trans zero) 0
    exact (by decide : (1 : Fin 256) ≠ 0) atZero
  · rename_i nonzero
    exact fun equal => nonzero equal.symm

theorem contains_injected {ops : AdapterRw.Ops} (port : ChildConeJoin ReadEvent ops)
    (read : ReadEvent) (outer : S2W_Trace.Log) (nonempty : outer ≠ [])
    (valid : ∀ event ∈ outer, S2W_TraceFacts.ValidEvent ops event) :
    read ∈ readEvents (full (children (inject port read)) outer) := by
  cases outer with
  | nil => exact False.elim (nonempty rfl)
  | cons event rest =>
    have returned := valid event (List.mem_cons_self ..)
    cases event with
    | returned call value =>
      have child := Op5I_EventCounterexample.returned port read call value returned
      apply List.mem_filterMap.mpr
      refine ⟨.child read, ?_, rfl⟩
      apply List.mem_flatMap.mpr
      refine ⟨.returned call value, List.mem_cons_self .., ?_⟩
      simp [expand, children, events, child]

theorem accepted_pair_carrier_counterexample {W A M Cv : Type} {N : Nat}
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
    (extraction : S2W_DigestExtraction.AeneasExtraction (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd) native1 native2 hashv)
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
    (port : ChildConeJoin ReadEvent (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)) (firstMarks : FirstMarks port) (secondMarks : SecondMarks port) :
    ∃ f s outer,
      SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
        e1.first (e2.second secondSizes) saved f s ∧
      runExpanded (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd) (children port)
        (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
          program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved, full (children port) outer) ∧
      runExpanded (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd) (children (inject port (wrong H)))
        (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
          program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved, full (children (inject port (wrong H))) outer) ∧
      FirstMarks (inject port (wrong H)) ∧ SecondMarks (inject port (wrong H)) ∧
      ¬ (∀ read ∈ readEvents (full (children (inject port (wrong H))) outer), read.2 = H read.1) ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd) e1.first (e2.second secondSizes) saved
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
          ClaimsUnrolledFinish.reference claimsStd claimsPrefix = ok (.Ok (retainedSem sem).claims)) := by
  obtain ⟨f, s, outer, pre, middle, fs, ss, cuts, expanded, owned, layout,
      unchanged, before1, before2, selected, caller⟩ :=
    ClaimsUnrolledSdk.accepted_pair_claims L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps ops B claimsStd native1 native2 hashv extraction sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
      p root length port firstMarks secondMarks
  have executed : S2W_Trace.run (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
      (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
        program e1.first data1 (e2.second secondSizes) data2 slot) [] = ok (.Ok saved, outer) := by
    rw [S2W_D189Interpretation.owned_account_frame] at owned
    cases h : S2W_Trace.run (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
        (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapterOps ops B claimsStd)
          program e1.first data1 (e2.second secondSizes) data2 slot) [] with
    | fail error => simp only [h, thenResult] at owned; cases owned
    | div => simp only [h, thenResult] at owned; cases owned
    | ok answer =>
      simp only [h, thenResult] at owned
      have fields := Result.ok.inj owned
      exact congrArg Result.ok (Prod.ext (congrArg Prod.fst fields) (congrArg (fun t => t.2.1) fields))
  have nonempty : outer ≠ [] := by
    intro empty
    have located := S2W_SiteSchedule.reached pre middle fs ss .tx1
    rw [← layout] at located
    simp [projected, full, empty] at located
  have valid := S2W_TraceFacts.run_valid _ _ [] outer (.Ok saved) (by simp) executed
  have member := contains_injected port (wrong H) outer nonempty valid
  refine ⟨f, s, outer, cuts, expanded, ?_, first_marks port (wrong H) firstMarks,
    second_marks port (wrong H) secondMarks, ?_, selected⟩
  · exact S2W_ExpandedTrace.execution_flatMap _ _ _ [] outer (.Ok saved) executed
  · intro consistent
    exact wrong_reply H (consistent (wrong H) member)

#print axioms wrong_reply
#print axioms contains_injected
#print axioms accepted_pair_carrier_counterexample
end AspisR1.Op5I_AcceptedCarrierCounterexample
end
