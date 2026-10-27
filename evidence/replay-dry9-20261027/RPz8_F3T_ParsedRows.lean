import RPz8_F3T_AlignedRows
import RPz7_PAln_RowBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ParsedRows
open AspisV8R19.DuplexFrames OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

theorem rows (wire : Bytes) (p : Parsed) (parsed : parse wire=some p) :
    semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic := by
  unfold parse at parsed
  split at parsed
  · contradiction
  · split at parsed
    · contradiction
    · cases hs : semanticRows 27 0 (slice wire 48 6983) with
      | none=>simp [hs] at parsed
      | some rs=>
        simp [hs] at parsed
        subst p
        exact hs

theorem bounds (wire : Bytes) (p : Parsed) (parsed : parse wire=some p) :
    ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D := by
  have header := parse_header wire p parsed
  have size : p.wire.length=57607 := by
    rw [header.2]
    exact ((OraclePortHeader.accepts_iff wire).mp header.1).1
  exact PAln_RowBounds.row_bound p (rows wire p parsed) size

#print axioms bounds
#print axioms rows
end AspisR1.F3T_ParsedRows
end
