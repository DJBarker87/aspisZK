import Hir_ObservedFailure
import Hist_InputUniqueness
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_CutBindingTransport
open Aeneas Aeneas.Std Result S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Exact source-to-consumer transport. Unlike SourceCuts alone, the TWO
actual validator/encoder observations explicitly bind both reconstructed TX2
public values. This obligation cannot be replaced by equality of lengths. -/
theorem same_pair (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (instruction : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (f g : FirstCut) (s t : SecondCut)
    (left : SourceCuts ops accounts1 accounts2 saved f s)
    (right : SourceCuts ops accounts1 accounts2 saved g t)
    (v w : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (validation1 : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id accounts2 instruction slot = ok (.Ok v))
    (validation2 : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id accounts2 instruction slot = ok (.Ok w))
    (encoding1 : ops.op22 v.statement = ok (.Ok s.encoded))
    (encoding2 : ops.op22 w.statement = ok (.Ok t.encoded)) (H : Bytes → State)
    (binding : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub) :
    S2W_AuthenticatedInputs.P2Prime H g.proof g.pub t.proof t.pub := by
  obtain ⟨proof1,pub1⟩ := Hist_InputUniqueness.first_bytes ops accounts1 accounts2 saved f g s t left right
  obtain ⟨proof2,checkpoint⟩ := Hist_InputUniqueness.second_proof_checkpoint ops accounts1 accounts2 saved f g s t left right
  have pub2 := Hist_InputUniqueness.second_public ops id accounts2 instruction slot s t v w
    validation1 validation2 encoding1 encoding2
  have gProof := DrvC_Bytes.slice_injective g.proof f.proof proof1
  have gPublic := DrvC_Bytes.slice_injective g.pub f.pub pub1
  have tProof := DrvC_Bytes.slice_injective t.proof s.proof proof2
  have tPublic := DrvC_Bytes.slice_injective t.pub s.pub pub2
  simpa only [gProof,gPublic,tProof,tPublic] using binding

#print axioms same_pair
end AspisR1.Hir_CutBindingTransport
end
