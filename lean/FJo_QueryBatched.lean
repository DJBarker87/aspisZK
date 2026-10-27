import FJo_OpeningDecodes
import FJo_PackedDecodes
import FJo_ActualOpening
import FJo_DotsBatched
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_QueryBatched
open Aeneas Aeneas.Std Result MultiproofConeCanonical AspisR1Stage2
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
attribute [local irreducible] TwoFoldExtraction.batchedWord
/-- SAME observed query with strict decodes and both initial packed maps DERIVED. -/
theorem value (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation ops proof p a out g none geo b bout)
    (openingSlot : ops.op11=Port4B_Opening.opening) (dotsSlot : ops.op20=FIp_DotsAdapter.dots)
    (size : proof.val.length=57607) (parsed : Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (queries : OraclePortSelectedDraft.queries tr=some q) (j : Fin 22) (index : a.next.val=j.val)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=data.gamma^l.val) :
    Port5Q1_OpeningValues.values o.dots=FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) (q j) := by
  have ho := o.opening_read
  rw [openingSlot] at ho
  have hd := o.dots_read
  rw [dotsSlot] at hd
  have literal := (FJo_ActualOpening.value proof size parsed wire a.next (by rw [index];exact j.isLt) o.opening ho).1
  rw [index] at literal
  obtain ⟨native,called,same⟩ := FIp_DotsAdapter.reached o.opening g o.dots hd
  obtain ⟨⟨c1,d1⟩,⟨c2,d2⟩⟩ := FJo_OpeningDecodes.value o.opening _ native called
  have p1 := d1
  have p2 := d2
  rw [literal] at p1 p2
  obtain ⟨mapped1,mapped2⟩ := FJo_PackedDecodes.value parsed q tr queries j c1 c2 p1 p2
  exact FJo_DotsBatched.value o.opening g o.dots parsed q tr data read j hg powers c1 c2 d1 d2 mapped1 mapped2 hd
#print axioms value
end AspisR1.FJo_QueryBatched
end
