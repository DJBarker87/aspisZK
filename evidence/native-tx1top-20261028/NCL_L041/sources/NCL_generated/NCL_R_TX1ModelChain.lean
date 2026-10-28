import RPx_Deployed
import NCL_R_WrapperToDriver
import NCL_R_DriverForward
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_TX1ModelChain
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open DrvC_Installation
attribute [local irreducible] AspisR1CurrentCaller.verifier.candidate.tx1

/-- Composed model path from the headline-shaped first-wrapper premise to
all same-run driver cuts. Native entry/snapshot/owned-body correspondence and
lower-unit domain discharge remain separate obligations, not new hypotheses
silently asserted by this model theorem. -/
theorem source {F C A : Type} (c : Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first (AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c))
      copy allocator e program data state = ok (.Ok (saved,post,final))) :
    post = writeBracket e.heap 2 0 0 (S2W_CommittedCheckpoint.source (nativeBytes saved)) ∧
    ∃ (raw pub proof : Slice U8) (semantic : Port1_Driver.Semantic),
      raw.val.length = 58295 ∧ proof.val.length = 57607 ∧
      raw.val = raw.val.take 688 ++ proof.val ∧
      Nonempty (NCL_DriverCuts.Cuts (currentInstalled c) (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof () saved) ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize () none = ok (.Ok saved) := by
  obtain ⟨write,pa,pu,pub,raw,stmt,sem,proof,split,_,_,_,_,_,_,_,range,len,same,called⟩ :=
    NCL_WrapperToDriver.source c copy std allocator e program data state final saved post accepted
  rw [same] at called
  have lengths := AdapterRw.Ranges.suffix_exact raw proof 688#usize 58295#usize
    (by scalar_tac) (by simpa using len) range
  obtain ⟨start,finish⟩ := SdkD_FoldedCut.installed_constants (current c) c.boundaries c.std
  obtain ⟨_,cuts⟩ := NCL_DriverCuts.accepted (currentInstalled c) (currentDigest c)
    (AspisS6CurrentVerifierCarrier.toPublic sem) pub proof 10#usize () saved start finish called
  exact ⟨write,raw,pub,proof,sem,len,by simpa using lengths.1,
    by simpa using lengths.2,cuts,called⟩
#print axioms source
end AspisR1.NCL_TX1ModelChain
end
