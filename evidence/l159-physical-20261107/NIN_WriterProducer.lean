import NHW_WriterFromNative
import NGR_HistoryPersist
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIN_WriterProducer
open Aeneas Aeneas.Std Result
open S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint MultiproofConeCanonical
open CheckpointBytes3Namespaces
theorem from_native {A C : Type}
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
 ∃ (prepared : CheckpointBytes5Writer.Prepared)
   (accumulator : CheckpointBytes5Writer.Accumulator)
   (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
   (hp hu hc : CheckpointBytes5Effect.Digest),
   saved = NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc ∧
   first n1 copy allocator e1 id data1 state1 = ok (.Ok
     (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc,post1,final1)) := by
 obtain ⟨semantic,publicBytes,proof,split,run,domain,hp,hu,hc,_,writer⟩ :=
   NHW_WriterFromNative.under_retained_extraction missing err r n1 n2 hashv extraction
     copy std allocator e1 id data1 state1 final1 saved post1 accepted
 refine ⟨_,_,domain,hp,hu,hc,?_,writer⟩
 have same := core.result.Result.Ok.inj (Result.ok.inj (accepted.symm.trans writer))
 exact congrArg Prod.fst same
#print axioms from_native
end AspisR1.NIN_WriterProducer
