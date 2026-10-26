import S2W_NativeConsolidation
import DrvC_Bytes
set_option autoImplicit false
namespace AspisR1.ARQ_FirstUniqueness
open Aeneas Aeneas.Std Result S2W_NativeConsolidation MultiproofConeCanonical

/-- Pure account reads and the exact suffix fix the public/proof operands
of all cuts on this same entry. Semantic getters are compared separately. -/
theorem bytes (ops : AdapterRw.Ops) (a1 a2 b2 : S2W_ExtractionBoundary.Accounts)
    (saved saved' : alloc.vec.Vec U8) (f g : FirstCut) (s t : SecondCut)
    (left : SourceCuts ops a1 a2 saved f s) (right : SourceCuts ops a1 b2 saved' g t) :
    f.pub = g.pub ∧ f.proof = g.proof := by
  have pa := Result.ok.inj (left.proof1Index.symm.trans right.proof1Index)
  have pu := Result.ok.inj (left.public1Index.symm.trans right.public1Index)
  have raw := right.proof1Read
  rw [←pa] at raw
  have rawEq := core.result.Result.Ok.inj (Result.ok.inj (left.proof1Read.symm.trans raw))
  have pub := right.public1Read
  rw [←pu] at pub
  have pubEq := core.result.Result.Ok.inj (Result.ok.inj (left.public1Read.symm.trans pub))
  have suffix := right.firstSuffix
  rw [←rawEq] at suffix
  have equal := List.append_cancel_left (left.firstSuffix.symm.trans suffix)
  exact ⟨pubEq,DrvC_Bytes.slice_injective _ _ equal⟩

/-- Once the actual semantic decoders are retained, their output too is
unique on the very same public bytes. -/
theorem semantic (ops : AdapterRw.Ops) (f g : FirstCut)
    (pub : f.pub = g.pub)
    (left : Port1_Driver.decodeSemantic ops f.pub = ok (some f.semantic))
    (right : Port1_Driver.decodeSemantic ops g.pub = ok (some g.semantic)) : f.semantic = g.semantic := by
  rw [←pub] at right
  exact Option.some.inj (Result.ok.inj (left.symm.trans right))

#print axioms bytes
#print axioms semantic
end AspisR1.ARQ_FirstUniqueness
