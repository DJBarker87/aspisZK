import F3T_AlignedRows
import PAln_RowBounds
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

#print axioms rows
end AspisR1.F3T_ParsedRows
end
