import RPx_Deployed
import NCL_R_TX1ModelChain
import NCL_R_WrapperWritten
import NCL_R_ShapeDomain
import NCL_R_InitialDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_TX1Saved
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open S2W_EntryWriteHistory MultiproofConeCanonical DrvC_Installation
attribute [local irreducible] AspisR1CurrentCaller.verifier.candidate.tx1

/-- First-wrapper model acceptance determines the exact saved bytes and
same-input driver cuts, with S2/proof/initial-accumulator domains derived.
The actual frozen Rust/lower-unit correspondence is still OPEN. -/
theorem source {F C A : Type} (c : Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (empty : e.heap.guards=[]) (zero : e.heap.counter (e.heap.accounts 2).1=0)
    (destination : (e.heap.payload (e.heap.accounts 2).1).descriptor.length=1768)
    (accepted : first (AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c))
      copy allocator e program data state=ok (.Ok (saved,post,final))) :
    saved.val.length=1768 ∧
    payloadBytes encode (post.payload (e.heap.accounts 2).1) 1768=bytesOf saved.val ∧
    post.ambient=e.heap.ambient ∧ post.accounts=e.heap.accounts ∧
    post.counter=e.heap.counter ∧
    (∀ cell, cell≠(e.heap.accounts 2).1 → post.payload cell=e.heap.payload cell) ∧
    ∃ (raw pub proof : Slice U8) (semantic : Port1_Driver.Semantic),
      raw.val.length=58295 ∧ proof.val.length=57607 ∧
      raw.val=raw.val.take 688++proof.val ∧
      ∃ cut : NCL_DriverCuts.Cuts (currentInstalled c) (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof () saved,
        cut.parsed=.S2 ∧ c.reserved=true ∧
        (Tx1Q_Carriers.accumulator cut.initial).weights.val=List.replicate 64 Port2_Initial.zeroK ∧
        (Tx1Q_Carriers.accumulator cut.initial).next=0#usize ∧
        AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
          (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize () none=ok (.Ok saved) := by
  obtain ⟨size,bytes,ambient,accounts,counter,frame⟩ := NCL_WrapperWritten.source _ copy std allocator e
    program data state final saved post empty zero destination accepted
  obtain ⟨_,raw,pub,proof,sem,rawLength,proofLength,suffix,⟨cut⟩,returned⟩ :=
    NCL_TX1ModelChain.source c copy std allocator e program data state final saved post accepted
  have shape := NCL_ShapeDomain.source c _ pub proof saved cut
  obtain ⟨reserved,weights,_,_,next⟩ := NCL_InitialDomain.source c _ pub proof saved cut
  exact ⟨size,bytes,ambient,accounts,counter,frame,raw,pub,proof,sem,
    rawLength,proofLength,suffix,cut,shape.1,reserved,weights,next,returned⟩
#print axioms source
end AspisR1.NCL_TX1Saved
end
