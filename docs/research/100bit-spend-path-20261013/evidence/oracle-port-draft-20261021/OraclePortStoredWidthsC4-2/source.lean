import OraclePortStoredParserC4

/-! Width and canonicality obligations come from strict stored parsing,
not from external assumptions on a recovered opening. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredWidthsC4
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft OraclePortSelectedDraft
attribute [local instance] Classical.propDecidable

theorem slice_length (b : Bytes) (offset size : Nat) (bound : offset+size ≤ b.length) :
    (slice b offset size).length = size := by
  simp only [slice,List.length_take,List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem parsed_length (b : Bytes) (p : Parsed) (parsed : parse b = some p) :
    p.wire.length = 57607 := by
  rw [(parse_header b p parsed).2]
  exact ((OraclePortHeader.accepts_iff b).mp (parse_header b p parsed).1).1

theorem parse_scan (b : Bytes) (p : Parsed) (parsed : parse b = some p) : scan p.wire := by
  rw [(parse_header b p parsed).2]
  by_contra bad
  simp [parse,bad] at parsed

theorem opening_width (b : Bytes) (p : Parsed) (parsed : parse b = some p)
    (pos : Nat) (bound : pos < 22) : (opening p pos).length = 832 := by
  apply slice_length
  rw [parsed_length b p parsed]
  omega

theorem opening_fields (b : Bytes) (p : Parsed) (parsed : parse b = some p)
    (pos : Nat) (bound : pos < 22) :
    ((opening p pos).take 480).length = 480 ∧
    (slice (opening p pos) 480 128).length = 128 ∧
    (slice (opening p pos) 608 32).length = 32 ∧
    (slice (opening p pos) 640 32).length = 32 ∧
    (slice (opening p pos) 672 128).length = 128 ∧
    (slice (opening p pos) 800 32).length = 32 := by
  have width := opening_width b p parsed pos bound
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [List.length_take,width]
  all_goals apply slice_length; rw [width]; decide

theorem opening_canonical (b : Bytes) (p : Parsed) (parsed : parse b = some p)
    (pos : Nat) (bound : pos < 22) : openingCanonical (opening p pos) :=
  (parse_scan b p parsed).2.2.2 pos (List.mem_range.mpr bound)

#print axioms slice_length
#print axioms parsed_length
#print axioms parse_scan
#print axioms opening_width
#print axioms opening_fields
#print axioms opening_canonical
end AspisR1.OraclePortStoredWidthsC4
end
