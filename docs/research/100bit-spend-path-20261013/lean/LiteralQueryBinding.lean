import R1LiteralQueryReadFacts
import R1LiteralQueryDensity

/-! Identify the literal row-31 event with the finite query-set event once the
strict query reader and matching-data reader both succeed. This is a
conditional event identity only; no sampler, acceptance, or extraction claim
is made here. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryBinding

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open AspisR1.LiteralQueryRead
open AspisR1.LiteralQueryReadFacts
open AspisR1.LiteralQueryDensity
open AspisR1.UnifiedQueryDensity
open AspisR1.MatchingSupport

theorem query_event_iff
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (xs : List Nat) (q : Fin 22 → Fin 262144)
    (d : MatchingSupport.Data AspisWideTower.WideExact)
    (state : AspisV8R19.SourceDuplexStep.State)
    (hround : P.round = 31)
    (hvalid : LiteralTranscript.valid 31 m)
    (hdata : LiteralMatchingData.atQuery P m = some d)
    (hdecode : LiteralQueryRead.decode xs = some q) :
    LiteralQueryDensity.bad P m
      (TranscriptView.Value.queries (.ok xs), state) ↔
      ((MatchingSupport.matchingSet d).card ≤ 9557 ∧
        ∀ j : Fin 22, q j ∈ MatchingSupport.matchingSet d) := by
  have hset := LiteralQueryReadFacts.chalSet_eq_univ_image xs q hdecode
  have hcard := LiteralQueryReadFacts.chalSet_card_eq_22 xs q hdecode
  have himage_card : (Finset.univ.image q).card = 22 := by
    rw [← hset]
    exact hcard
  have hlen : (LiteralTranscript.erasePrefix P).rounds.length = 31 := by
    simpa only [LiteralTranscript.erasePrefix, List.length_map, FS.Prefix.round] using hround
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hvalid
  | c2 bytes word => simp [LiteralTranscript.valid] at hvalid
  | second bytes word => simp [LiteralTranscript.valid] at hvalid
  | payload bytes =>
      simp only [LiteralQueryDensity.bad, hround, hvalid, true_and,
        UnifiedQueryDensity.queryBad, hlen, LiteralTranscript.erase,
        LiteralQueryDensity.selectedSet, hdata, Option.map_some]
      rw [hset, himage_card]
      simp only [true_and]
      constructor
      · rintro ⟨hc, hsub⟩
        exact ⟨hc, fun j => hsub (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)⟩
      · rintro ⟨hc, hq⟩
        refine ⟨hc, ?_⟩
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
        exact hq j

#print axioms query_event_iff

end AspisR1.LiteralQueryBinding
end
