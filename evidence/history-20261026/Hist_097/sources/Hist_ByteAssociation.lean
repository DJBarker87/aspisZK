import Hist_InputUniqueness
import Hist_ByteExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ByteAssociation
open Aeneas Aeneas.Std Result S2W_NativeConsolidation
open MultiproofConeCanonical

private theorem inputs_ext {a b : R9PoolRuntimeBinding.Inputs}
    (hp : a.proof = b.proof) (hu : a.pub = b.pub) : a = b := by
  cases a; cases b; cases hp; cases hu; rfl

/-- The byte output required by the containing experiment is independent of
which full source witness a factory selected for THIS SAME execution. The
actual validation/encoder returns are essential to pin the second public. -/
theorem unique (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (a1 a2 : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (f g : FirstCut) (s t : SecondCut)
    (v w : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (left : SourceCuts ops a1 a2 saved f s) (right : SourceCuts ops a1 a2 saved g t)
    (vl : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program a2 data slot = ok (.Ok v))
    (vr : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program a2 data slot = ok (.Ok w))
    (el : ops.op22 v.statement = ok (.Ok s.encoded))
    (er : ops.op22 w.statement = ok (.Ok t.encoded)) :
    Hist_PairExperiment.select ⟨g,t⟩ = Hist_PairExperiment.select ⟨f,s⟩ := by
  obtain ⟨p1,u1⟩ := Hist_InputUniqueness.first_bytes ops a1 a2 saved f g s t left right
  obtain ⟨p2,_⟩ := Hist_InputUniqueness.second_proof_checkpoint ops a1 a2 saved f g s t left right
  have u2 := Hist_InputUniqueness.second_public ops program a2 data slot s t v w vl vr el er
  apply Prod.ext
  · exact inputs_ext p1 u1
  · exact inputs_ext p2 u2

#print axioms unique
end AspisR1.Hist_ByteAssociation
end
