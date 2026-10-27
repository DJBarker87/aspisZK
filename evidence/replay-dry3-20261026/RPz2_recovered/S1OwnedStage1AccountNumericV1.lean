import S1OwnedStage1ExtractedChildrenV1
import S1PrepareNumericV1
import S6CurrentStage1FirstFieldsV1
import S1AcceptedSemanticNumericV1
set_option autoImplicit false
namespace AspisS1ValuesOwnedInstallation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation



/-- Same accepted owned stage1, retaining the actual decoded statement, preparation,
roots, scratch, continuation and every Y1 field parse. Numeric ranges are derived
for the SAME returned semantic object. SDK/native interpretation remains open. Actual account indices and reads are
retained on the SAME byte/proof/statement/preparation witnesses. -/
theorem owned_stage1_account_numeric (adapterOps : AdapterRw.Ops) (ops : Ops)

    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
    (data : Slice U8) (out : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned
      (AspisS6CurrentFirstInstallation.install adapterOps (NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      program accounts data=ok (.Ok out)) :
    ∃ (proofAccount publicAccount : AdapterRw.r1_pool_adapter.owned.OwnedAccount)
      (rawProof : Slice U8) (start finish : Usize) (bytes proof : Slice U8) (split : Usize)
      (statement : AspisR1PublicPreparation.FirstCaller.DecoderStatement),
      Slice.index_usize accounts 0#usize=ok proofAccount ∧
      Slice.index_usize accounts 1#usize=ok publicAccount ∧
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
  let installed := NativeBuffers.install (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B
  obtain ⟨pa,pu,bytes,raw,decoded,semantic,proof,split,start,finish,encoded,
    ip,iu,rp,ru,dc,nativeDecode,enc,sameBytes,valid,selected,ranged,called,length,first⟩ :=
    AspisS6CurrentStage1FirstFields.accepted_stage1 adapterOps installed
      program accounts data out accepted
  obtain ⟨statement,pub,hd,hpub,htx⟩ := AspisR1PublicPreparation.RepinS6First.first_success
    AdapterRw.solana_program_error.ProgramError.InvalidAccountData
    (FirstComposition.currentTx1 installed
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
    (fun error => adapterOps.op44 (AspisS6CurrentVerifierCarrier.fromError error))
    bytes proof split out first
  subst pub
  change verifier.candidate.tx1 installed
    (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    (FirstComposition.toCurrentPublic
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
    bytes proof split () none=ok (.Ok out) at htx
  obtain ⟨hk,variant,zero,prepared,scratch,hvariant,hcheck,hzero,hprepare,tail⟩ :=
    Tx1Reachability.tx1_success installed
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      (FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
      bytes proof split () out htx
  obtain ⟨root0,root1,hroots,hphysical0,hphysical1⟩ :=
    NativeBuffers.prepare_physical_roots (withValues ops) nativeValues
      AspisS1ExtractedRoundChildren.children B
      (fun i o s u h => length_frame i o u s h)
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  obtain ⟨stored,initial,semanticBytes,view,sem,storedCall,expanded,storedLength,
    initialLength,y1Length,byteEq,viewCall,semanticCall,newCall,numeric,fields⟩ :=
    prepare_numeric ops B
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ proof () prepared (Array.repeat 29#usize zero) scratch hprepare
  exact ⟨pa,pu,raw,start,finish,bytes,proof,split,statement,
    ip,iu,rp,ru,ranged,length,hd,hk,zero,prepared,scratch,root0,root1,
    hprepare,hroots,hphysical0,hphysical1,tail,stored,initial,semanticBytes,view,sem,
    storedCall,expanded,storedLength,initialLength,y1Length,byteEq,viewCall,
    semanticCall,newCall,numeric,fields⟩

#print axioms owned_stage1_account_numeric
end AspisS1ValuesOwnedInstallation
