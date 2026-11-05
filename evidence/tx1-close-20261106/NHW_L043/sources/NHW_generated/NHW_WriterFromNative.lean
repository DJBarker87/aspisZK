import NHW_SourceSelection
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_WriterFromNative
open Aeneas Aeneas.Std Result
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint MultiproofConeCanonical
open CheckpointBytes3Namespaces
/-- Exact NGR producer equation under the headline's RETAINED whole-source
extraction interpretation. This is not the new direct-(ai) driver certificate:
that route still requires native verify_observed's full-Result op9 packet.
All source/read/preparation/query/finish witnesses are derived from acceptance. -/
theorem under_retained_extraction {A C : Type}
 (missing : IDa_Deployed.Uninstalled C) (err : C) (r : NP6_StdModel.Reservation)
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction
   (DrvC_Installation.sdk (NHW_DeployedQuery.configuration missing err r)) n1 n2 hashv)
 (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
 (std : TrustedStd copy) (allocator : Allocator A) (e1 : Entry)
 (id : S2W_ExtractionBoundary.Program) (data1 : Slice U8) (state1 final1 : A)
 (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
 (accepted : first n1 copy allocator e1 id data1 state1=ok (.Ok (saved,post1,final1))) :
 ∃ (semantic : AdapterRw.LeadInputs.Public) (publicBytes proof : Slice U8) (split : Usize),
 ∃ run : Tx1Q_Execution.Run
   (DrvC_Installation.currentInstalled (NHW_DeployedQuery.configuration missing err r))
   (NHW_DeployedQuery.configuration missing err r).reserved
   (NHW_DeployedQuery.configuration missing err r).query
   (NHW_DeployedQuery.configuration missing err r).geometry
   (DrvC_Installation.currentDigest (NHW_DeployedQuery.configuration missing err r)) ()
   (AspisS6CurrentVerifierCarrier.toPublic semantic) publicBytes proof split saved,
 ∃ domain : NGC_KNE_Caller.WriterDomain (toPrepared (Tx1Q_Carriers.prepared run.p))
   (toAccumulator (Tx1Q_Carriers.accumulator
     {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})),
 ∃ hp hu hc : CheckpointBytes5Effect.Digest,
 AdapterRw.first_decoded (DrvC_Installation.sdk (NHW_DeployedQuery.configuration missing err r))
   semantic publicBytes proof split=ok (.Ok saved) ∧
 first n1 copy allocator e1 id data1 state1=ok (.Ok
   (NGC_KNE_Writer.returned (toPrepared (Tx1Q_Carriers.prepared run.p))
     (toAccumulator (Tx1Q_Carriers.accumulator
       {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩})) domain hp hu hc,post1,final1)) := by
 let c := NHW_DeployedQuery.configuration missing err r
 have native := (S2W_D189Wrappers.first_accepted n1 copy std allocator e1 id data1 state1 final1 saved post1 accepted).1
 obtain ⟨pa,pu,publicBytes,raw,statement,semantic,proof,split,_,_,_,_,_,firstCall,_,_⟩ :=
   S2W_ExtractionBoundary.native_first_fields (DrvC_Installation.sdk c) n1 n2 hashv
     (S2W_DigestExtraction.sourceBoundary _ _ _ _ extraction) id e1.first data1 saved native
 have tx : AspisR1CurrentCaller.verifier.candidate.tx1 (DrvC_Installation.currentInstalled c)
   (DrvC_Installation.currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
   publicBytes proof split () none=ok (.Ok saved) :=
   AspisS6CurrentFirstInstallation.current_success _ _ semantic publicBytes proof split () saved
     (AspisS6CurrentStage1CodecJoin.first_success _ semantic publicBytes proof split saved firstCall)
 have tx' := tx
 rw [show c=F3V_Install.configuration c from (NHW_SourceSelection.fixed missing err r).symm] at tx'
 have packet := NHW_ModelWriter.source missing err r
   (DrvC_Installation.currentDigest c) () (AspisS6CurrentVerifierCarrier.toPublic semantic)
   publicBytes proof split saved tx'
 simp only [NHW_SourceSelection.fixed] at packet
 obtain ⟨run,domain,writer⟩ := packet
 unfold NHW_CheckpointPort.source at writer
 obtain ⟨bytes,call,last⟩ := Port3_PushFrame.bind_success _ _ _ writer
 have byteSame : bytes=saved := Result.ok.inj last
 subst bytes
 obtain ⟨hp,hu,hc,_,_,_,same⟩ := NHW_WriterReplies.source _ () _ _ domain proof publicBytes saved call
 refine ⟨semantic,publicBytes,proof,split,run,domain,hp,hu,hc,firstCall,?_⟩
 rw [←same]
 exact accepted
#print axioms under_retained_extraction
end AspisR1.NHW_WriterFromNative
