import NDO_JFv_SemanticChain
import RPz7_PSem_SemanticTrace
set_option autoImplicit false
namespace AspisR1.JFv_Sampler25
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

def rows : List U8 := ExtractedPrefixTrace.rowOrder.take 25

theorem source {H : Type} (D : aspis_core.Digest32 H) (total : JFv_TranscriptTotal.Total D)
    (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (initial : t.next_row.val=0) :
    ∃ (after : r1_wire.SemanticTranscript H) (cs : List (SourceFull25.Call D pre)),
      SourceFull25.Trace D pre t after cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      cs.map (fun c => c.record.framed)=pre.records.val.take 25 ∧
      (∀ q ∈ cs.map SourceFull25.Call.q,JFv_RoundArithmetic.Canonical q) := by
  obtain ⟨after,qs,run,canonical⟩ := JFv_SemanticChain.success D total pre rows 0 t initial rfl (by decide)
  obtain ⟨cs,trace,order,sampled,frames⟩ := SourceFull25.run_full25_frames D pre run (by rfl)
  refine ⟨after,cs,trace,?_,frames,?_⟩
  · have equal := congrArg (List.map UScalar.val) order
    have expected : rows.map UScalar.val=List.range 25 := rfl
    rw [expected] at equal
    simpa only [List.map_map,Function.comp_def] using equal
  · rw [sampled];exact canonical

#print axioms source
end AspisR1.JFv_Sampler25
