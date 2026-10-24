import S1SdkStage1AccountNumericV1
import S6SdkEnclosingCutsV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_NativeConsolidation
/-- One accepted interpreted SDK wrapper derives preparation/numeric witnesses
on EVERY published enclosing source cut, using its original full decoded
statement and actual public/proof/split. No reconstructed identity is assumed. -/
theorem sdk_stage1_source_cut_numeric {W A : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e : Entry) (world : W)
    (admission : S2W_D189Consolidation.RuntimeEntrypointAdmission L e world 3)
    (adapterOps : AdapterRw.Ops) (ops : Ops)

    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      native1 native2 hashv)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (initial final : A) (post : Heap (Nat → Record))
    (accepted : S2W_D189Wrappers.first native1 copy allocator e program data initial =
      ok (.Ok (out,post,final))) :
    post = writeBracket e.heap 2 0 0 (source (nativeBytes out)) ∧
    S2W_AccountObservations.observe encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient 1 ∧
    ∀ (accounts2 : Slice AdapterRw.Cuts.Account) (f : FirstCut) (s : SecondCut),
      SourceCuts (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
        e.first accounts2 out f s →
      f.pub = e.buffers (e.handles 1).1 ∧ f.pub.val.length = 1880 ∧
      payloadBytes encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length =
          MultiproofConeCanonical.bytesOf f.pub.val ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual f.pub =
        ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)) ∧
      f.split = compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
          f.proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=f.proof.val.slice 16 48 ∧ root1.val=f.proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          f.pub f.proof f.split () none prepared scratch=ok (.Ok out) ∧
        ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit),
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            f.proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),view.y1) ∧
          stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
          (∀ j, j<928 → view.y1.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
          sourceView f.proof semantic view.y1=ok (.Ok view) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            view.semantic () none=ok (.Ok sem) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op8
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
          AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
          ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
            AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
            AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  obtain ⟨written,frame,allCuts⟩ := AspisS6SdkEnclosingCuts.accepted_sdk_all_cuts
    L sdk copy std allocator e world admission adapterOps
    (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    native1 native2 hashv extraction program data initial final out post accepted
  refine ⟨written,frame,?_⟩
  intro accounts2 f s cuts
  obtain ⟨buffer,size,observed,encoded,decoded,nativeDecode,encodedCall,encodedBytes,split,first⟩ :=
    allCuts accounts2 f s cuts
  let installed := NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B
  obtain ⟨statement,pub,hd,hpub,htx⟩ := AspisR1PublicPreparation.RepinS6First.first_success
    AdapterRw.solana_program_error.ProgramError.InvalidAccountData
    (FirstComposition.currentTx1 installed
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
    (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error))
    f.pub f.proof f.split out first
  have sameStatement := core.result.Result.Ok.inj (Result.ok.inj (hd.symm.trans nativeDecode))
  subst statement
  subst pub
  change verifier.candidate.tx1 installed
    (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    (FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic
        (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
    f.pub f.proof f.split () none=ok (.Ok out) at htx
  obtain ⟨hk,variant,zero,prepared,scratch,hvariant,hcheck,hzero,hprepare,tail⟩ :=
    Tx1Reachability.tx1_success installed
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ f.pub f.proof f.split () out htx
  obtain ⟨root0,root1,hroots,hphysical0,hphysical1⟩ :=
    NativeBuffers.prepare_physical_roots (withValues ops) nativeValues
      AspisS1ExtractedRoundChildren.children B
      (fun i o st u h => length_frame i o u st h)
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ f.proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  obtain ⟨stored,initialBytes,semanticBytes,view,sem,storedCall,expanded,storedLength,
    initialLength,y1Length,byteEq,viewCall,semanticCall,newCall,numeric,fields⟩ :=
    prepare_numeric ops B
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ f.proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  exact ⟨buffer,size,observed,nativeDecode,split,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,stored,initialBytes,semanticBytes,view,sem,
    storedCall,expanded,storedLength,initialLength,y1Length,byteEq,viewCall,
    semanticCall,newCall,numeric,fields⟩

#print axioms sdk_stage1_source_cut_numeric
end AspisS1ValuesOwnedInstallation
