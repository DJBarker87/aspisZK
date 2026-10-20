import CanonicalCutEnrichedTranscript
import R1LiteralByteProtocol

set_option autoImplicit false
noncomputable section
namespace AspisR1.RawEnrichedRowsScheduleTransport

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralTranscript

private theorem valid_enrichMessage (w : Words) (i : Nat) (m : Message) :
    LiteralTranscript.valid i (enrichMessage w m) ↔ LiteralTranscript.valid i m := by
  cases m with
  | initial root word =>
      by_cases hi : i = 0
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | payload bytes => simp [LiteralTranscript.valid, enrichMessage]
  | c2 bytes word =>
      by_cases hi : i = 2
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]
  | second bytes word =>
      by_cases hi : i = 30
      · subst i; simp [LiteralTranscript.valid, enrichMessage]
      · simp [LiteralTranscript.valid, enrichMessage, hi]

/-- List-level schedule transport, independent of transcript recursion. -/
theorem valid_original_of_enrichedRows
    (w : Words) (originalRows enrichedRows : List (Message × Challenge))
    (pf : LiteralProtocol.Proof)
    (hrows : enrichedRows = enrichRounds w originalRows)
    (hvalid : ∀ i, i ≤ 30 → ∃ m c,
      enrichedRows[i]? = some (m,c) ∧ LiteralTranscript.valid i m)
    (hindex : ∀ i, i < 33 → ∃ c, originalRows[i]? = some (pf i,c)) :
    ∀ i, i ≤ 30 → LiteralTranscript.valid i (pf i) := by
  intro i hi
  have hi33 : i < 33 := by omega
  obtain ⟨c, hget⟩ := hindex i hi33
  obtain ⟨m, c', hrow, hv⟩ := hvalid i hi
  rw [hrows] at hrow
  have hmapped : (enrichRounds w originalRows)[i]? =
      some (enrichMessage w (pf i), c) := by
    simp only [enrichRounds, List.getElem?_map]
    rw [hget]
    rfl
  have hp : (m,c') = (enrichMessage w (pf i),c) :=
    Option.some.inj (hrow.symm.trans hmapped)
  have hm : m = enrichMessage w (pf i) := congrArg Prod.fst hp
  have hv' : LiteralTranscript.valid i (enrichMessage w (pf i)) := by
    simpa only [hm] using hv
  exact (valid_enrichMessage w i (pf i)).mp hv'

#print axioms valid_original_of_enrichedRows
end AspisR1.RawEnrichedRowsScheduleTransport
end
