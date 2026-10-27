import RPz7_S1OwnedStage1AccountNumericV1
import RPz7_SInt2_S6SdkStage1ReuseFactoredV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation
open AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint



/-- Same accepted owned stage1, retaining the actual decoded statement, preparation,
roots, scratch, continuation and every Y1 field parse. Numeric ranges are derived
for the SAME returned semantic object. SDK/native interpretation remains open. Actual account indices and reads are
retained on the SAME byte/proof/statement/preparation witnesses. -/
theorem sdk_stage1_account_numeric {W A : Type}
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
    ∃ (proofAccount publicAccount : AdapterRw.r1_pool_adapter.owned.OwnedAccount)
      (rawProof : Slice U8) (start finish : Usize) (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      bytes = e.buffers (e.handles 1).1 ∧ bytes.val.length = 1880 ∧
      payloadBytes encode (L.cellPayload world (L.accountData world 1))
        (L.cellPayload world (L.accountData world 1)).descriptor.length =
          MultiproofConeCanonical.bytesOf bytes.val ∧
      S2W_AccountObservations.observe encode e.metadata 3 post 1 =
        S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient 1 ∧
      Slice.index_usize e.first 0#usize=ok proofAccount ∧
      Slice.index_usize e.first 1#usize=ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
        (AspisS6CurrentFirstInstallation.install adapterOps
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
        proofAccount=ok (.Ok rawProof) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
        (AspisS6CurrentFirstInstallation.install adapterOps
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
        publicAccount=ok (.Ok bytes) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        rawProof {start:=start,«end»:=finish}=ok proof ∧
      Slice.len rawProof=finish ∧
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual bytes=ok (.Ok statement) ∧
      split=compact.SPLIT ∧
      ∃ (zero : aspis_core.field.wide_exact.WideExact) (prepared : verifier.Prepared)
        (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
        (root0 root1 : Array U8 32#usize),
        verifier.candidate.prepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
          proof () none (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
        prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 ∧
        Tx1Reachability.afterPrepare (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B) (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
          bytes proof split () none prepared scratch=ok (.Ok out) ∧
        ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit),
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),view.y1) ∧
          stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
          (∀ j, j<928 → view.y1.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
          sourceView proof semantic view.y1=ok (.Ok view) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            view.semantic () none=ok (.Ok sem) ∧
          (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B).op8
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
            sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
          AspisS1SemanticArrayRanges.CurrentVerifiedNumeric sem ∧
          ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
            AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
            AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  obtain ⟨native,written⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator
    e program data initial final out post accepted
  have owned : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps
        (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      program e.first data = ok (.Ok out) :=
    (extraction.stage1 program e.first data).symm.trans native
  obtain ⟨pa,pu,raw,start,finish,bytes,proof,split,statement,
    ip,iu,rp,ru,ranged,length,hd,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,stored,initialBytes,semanticBytes,view,sem,
    storedCall,expanded,storedLength,initialLength,y1Length,byteEq,viewCall,
    semanticCall,newCall,numeric,fields⟩ :=
    owned_stage1_account_numeric adapterOps ops B program e.first data out owned
  have sameAccount := Result.ok.inj (iu.symm.trans (first_index e).2.1)
  subst pu
  obtain ⟨buffer,size⟩ := AspisS6SdkStage1ReuseFactored.public_read e _ bytes ru
  have observed := native_buffer e L sdk world admission.related admission.entry.valid 1
  rw [← buffer] at observed
  have disjoint := first_disjoint e _ program data out owned
  have frame := S2W_AccountObservations.write_frame encode e.metadata 3 e.heap 2 0 0
    (source (nativeBytes out)) rfl rfl 1 (fun _ => disjoint 1 (by decide) (by decide))
  have initialObservation := S2W_D189Interpretation.native_observation L sdk encode e.metadata 3
    world e.heap admission.related admission.entry.valid
  have publicFrame : S2W_AccountObservations.observe encode e.metadata 3 post 1 =
      S2W_D189Interpretation.nativeObserve L encode e.metadata 3 world e.heap.ambient 1 := by
    rw [written]
    exact frame.trans ((congrFun initialObservation 1).symm)
  exact ⟨written,pa,e.snapshot 1 1880 1880,raw,start,finish,bytes,proof,split,statement,
    buffer,size,observed,publicFrame,ip,iu,rp,ru,ranged,length,hd,hk,
    zero,prepared,scratch,root0,root1,hprepare,hroots,hphysical0,hphysical1,tail,
    stored,initialBytes,semanticBytes,view,sem,storedCall,expanded,storedLength,
    initialLength,y1Length,byteEq,viewCall,semanticCall,newCall,numeric,fields⟩

#print axioms sdk_stage1_account_numeric
end AspisS1ValuesOwnedInstallation
