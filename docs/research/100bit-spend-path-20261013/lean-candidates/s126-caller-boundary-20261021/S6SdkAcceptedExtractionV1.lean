import S6SdkFirstOnlyV1
set_option autoImplicit false
noncomputable section
namespace AspisS6SdkAcceptedExtraction
open Aeneas Aeneas.Std Result
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation AspisS6CurrentFirstInstallation AspisS6CurrentVerifierCarrier
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier

/-- Same complete first-stage carriers and exact accepted output; permits
native allocation abort/rejection without requiring an equal erased-source
abort. This is an ACCEPTED-ONLY source-refinement premise, not its instance. -/
def AcceptedStage1Extraction (ops : AdapterRw.Ops)
    (native1 : S2W_ExtractionBoundary.First) : Prop :=
  ∀ program accounts data saved,
    native1 program accounts data = ok (.Ok saved) →
    AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data = ok (.Ok saved)

theorem of_full (ops : AdapterRw.Ops) (native1 : S2W_ExtractionBoundary.First)
    (full : AspisS6SdkFirstOnly.Stage1Extraction ops native1) :
    AcceptedStage1Extraction ops native1 := by
  intro program accounts data saved accepted
  exact (full program accounts data).symm.trans accepted

/-- Original complete SDK/account/checkpoint theorem using only the accepted
first-stage source refinement. Every conclusion and other premise is unchanged.
No SourceCuts, second-stage success, heap headroom or decoder success is input. -/
theorem original_sdk_reached_first_accepted_extraction {W A : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry) (world : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (ops : AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (native1 : S2W_ExtractionBoundary.First)
    (stage1 : AcceptedStage1Extraction (install ops vops) native1)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8)
    (initial final : A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : AspisS6SdkFirstObjectEquivalence.originalFirst native1 copy allocator e program data initial =
      ok (.Ok (saved,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes saved)) ∧
    S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 ∧
    ∃ f : FirstCut,
      Slice.index_usize e.first 0#usize = ok f.proofAccount ∧
      Slice.index_usize e.first 1#usize = ok f.publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops vops) f.proofAccount = ok (.Ok f.raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (install ops vops) f.publicAccount = ok (.Ok f.pub) ∧
      (install ops vops).op47 f.pub = ok (.Ok f.statement) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.first_decoded (install ops vops) f.semantic f.pub f.proof f.split = ok (.Ok saved) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        f.raw {start := 688#usize, «end» := 58295#usize} = ok f.proof ∧
      f.raw.val.length = 58295 ∧
      f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧
      payloadBytes S2W_ReturnedCheckpoint.encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length = MultiproofConeCanonical.bytesOf f.pub.val ∧
      ∃ encoded,
        AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 f.pub =
          ok (.Ok (toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
        AspisS6CurrentCodecInstallation.encode f.statement = ok (.Ok encoded) ∧ encoded.val = f.pub.val ∧
        AspisR1CurrentCaller.FirstComposition.firstCurrent
          AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
          (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
          (fun error => ops.op44 (fromError error)) f.pub f.proof f.split = ok (.Ok saved) := by
  have wrapper : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (saved,post,final)) := by
    rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]
    exact accepted
  obtain ⟨native,written⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final saved post wrapper
  have owned := stage1 program e.first data saved native
  have distinct := first_disjoint e (install ops vops) program data saved owned
  have publicFrame := S2W_AccountObservations.write_frame S2W_ReturnedCheckpoint.encode e.metadata 3 e.heap 2 0 0
    (source (nativeBytes saved)) rfl rfl 1 (fun _ => distinct 1 (by decide) (by decide))
  have initialObservation := S2W_D189Interpretation.native_observation L sdk S2W_ReturnedCheckpoint.encode e.metadata 3
    world e.heap admission.related admission.entry.valid
  have frame : S2W_AccountObservations.observe S2W_ReturnedCheckpoint.encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L S2W_ReturnedCheckpoint.encode e.metadata 3 world e.heap.ambient 1 := by
    rw [written]
    exact publicFrame.trans ((congrFun initialObservation 1).symm)
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dc,selected,ranged,called,length⟩ :=
    AdapterRw.Accepted.first_call (install ops vops) program e.first data saved owned
  have samePu := Result.ok.inj (iu.symm.trans (first_index e).2.1)
  have pubRead := ru
  rw [samePu] at pubRead
  obtain ⟨buffer,size⟩ := AspisS6SdkStage1ReuseFactored.public_read e (install ops vops) pub pubRead
  have observed := native_buffer e L sdk world admission.related admission.entry.valid 1
  rw [← buffer] at observed
  have decoded : decode pub = ok (.Ok statement) := dc
  have nativeDecode := decode_success pub statement decoded
  obtain ⟨encoded,encodedCall,bytes⟩ := accepted_inverse pub statement decoded
  have tx := current_success vops _ semantic pub proof split () saved
    (AspisS6CurrentStage1CodecJoin.first_success (install ops vops) semantic pub proof split saved called)
  have selection := selected_public statement
  rw [selected] at selection
  rw [Result.ok.inj selection] at tx
  have first : AspisR1CurrentCaller.FirstComposition.firstCurrent
      AdapterRw.solana_program_error.ProgramError.InvalidAccountData vops
      (toDigest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install ops vops)))
      (fun error => ops.op44 (fromError error)) pub proof split = ok (.Ok saved) := by
    unfold AspisR1CurrentCaller.FirstComposition.firstCurrent
    rw [AspisR1PublicPreparation.RepinS6First.reuse_decoded _ _ _ _ _ _ _ nativeDecode]
    unfold AspisR1PublicPreparation.RepinS6First.first_decoded
      AspisR1PublicPreparation.RepinS6First.observer
      AspisR1CurrentCaller.FirstComposition.currentTx1
    simp only [bind_tc_ok,Option.map_none,tx,AspisR1PublicPreparation.core.result.Result.map_err]
  exact ⟨written,frame,⟨pa,pu,raw,pub,statement,semantic,proof,split⟩,
    ip,iu,rp,ru,dc,selected,called,ranged,length,buffer,size,observed,
    encoded,nativeDecode,encodedCall,bytes,first⟩


#print axioms of_full
#print axioms original_sdk_reached_first_accepted_extraction
end AspisS6SdkAcceptedExtraction
end
