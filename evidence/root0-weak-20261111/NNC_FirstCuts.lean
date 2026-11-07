import NNC_FirstWriter
import NNC_SourceCuts
set_option autoImplicit false
noncomputable section
namespace NNC_FirstCuts
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- The writer half of Cuts, with no reader occurrence at all. -/
structure Facts (ops : AdapterRw.Ops) (accounts : S2W_ExtractionBoundary.Accounts)
 (saved : alloc.vec.Vec U8) (f : FirstCut) : Prop where
 proofIndex : Slice.index_usize accounts 0#usize=ok f.proofAccount
 publicIndex : Slice.index_usize accounts 1#usize=ok f.publicAccount
 proofRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.proofAccount=ok (.Ok f.raw)
 publicRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops f.publicAccount=ok (.Ok f.pub)
 decode : ops.op47 f.pub=ok (.Ok f.statement)
 first : AdapterRw.first_decoded ops f.semantic f.pub f.proof f.split=ok (.Ok saved)
 proofLength : (bytesOf f.proof.val).length=57607
 suffix : bytesOf f.raw.val=(bytesOf f.raw.val).take 688++bytesOf f.proof.val

/-- TX1 native success gives its own source cut; no accepted2 or second
SourceCuts packet is required. All witnesses are obtained from this call. -/
theorem native (ops : AdapterRw.Ops)
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction ops n1 n2 hashv)
 (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
 (data : Slice U8) (saved : alloc.vec.Vec U8)
 (accepted : n1 id accounts data=ok (.Ok saved)) :
 ∃ f, Facts ops accounts saved f := by
 obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dec,first,len,shape⟩ :=
  S2W_ExtractionBoundary.native_first_fields ops n1 n2 hashv (S2W_DigestExtraction.sourceBoundary ops n1 n2 hashv extraction) id accounts data saved accepted
 exact ⟨⟨pa,pu,raw,pub,statement,semantic,proof,split⟩,⟨ip,iu,rp,ru,dec,first,len,shape⟩⟩

/-- Fully derived writer side of NMF', at its native TX1 cut. The surviving
per-call oracle interpretation is the existing runtime item. -/
theorem writer {F C : Type} (c : DrvC_Installation.Configuration F C)
 (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
 (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
 (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk c) n1 n2 hashv)
 (id : S2W_ExtractionBoundary.Program) (accounts : S2W_ExtractionBoundary.Accounts)
 (data : Slice U8) (saved : alloc.vec.Vec U8) (H : Bytes → State)
 (oracle : CheckpointBytes5Inputs.Oracle
  (VTop_Checkpoint.digest (Tx1Q_Install.digest (DrvC_Installation.currentDigest c))) () H)
 (accepted : n1 id accounts data=ok (.Ok saved)) :
 ∃ f, Facts (DrvC_Installation.sdk c) accounts saved f ∧
  NLP_InputDomain.Root0 saved.deref f.proof ∧
  NLW_ReaderHeader.decode (bytesOf saved.val)=some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)) := by
 obtain ⟨f,cut⟩ := native _ n1 n2 hashv extraction id accounts data saved accepted
 exact ⟨f,cut,NNC_FirstWriter.facts c f.semantic f.pub f.proof f.split saved H oracle cut.first⟩
#print axioms native
#print axioms writer
end NNC_FirstCuts
