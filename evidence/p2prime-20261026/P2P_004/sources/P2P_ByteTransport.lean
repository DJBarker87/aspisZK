import Hist_ByteAssociation
import P2P_Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_ByteTransport
open Aeneas Aeneas.Std Result S2W_NativeConsolidation MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem same_pair (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (a1 a2 : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (f g : FirstCut) (s t : SecondCut)
    (v w : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (left : SourceCuts ops a1 a2 saved f s) (right : SourceCuts ops a1 a2 saved g t)
    (vl : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id a2 data slot = ok (.Ok v))
    (vr : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id a2 data slot = ok (.Ok w))
    (el : ops.op22 v.statement = ok (.Ok s.encoded))
    (er : ops.op22 w.statement = ok (.Ok t.encoded)) (H : Bytes → State) :
    S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub ↔
    S2W_AuthenticatedInputs.P2Prime H g.proof g.pub t.proof t.pub := by
  have same := Hist_ByteAssociation.unique ops id a1 a2 data slot saved f g s t v w left right vl vr el er
  change R9PoolRuntimeBinding.P2Prime H (Hist_PairExperiment.select ⟨f,s⟩).1
    (Hist_PairExperiment.select ⟨f,s⟩).2 ↔
    R9PoolRuntimeBinding.P2Prime H (Hist_PairExperiment.select ⟨g,t⟩).1
    (Hist_PairExperiment.select ⟨g,t⟩).2
  rw [same]

#print axioms same_pair
end AspisR1.P2P_ByteTransport
end
