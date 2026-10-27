import R1Z.PV_CB_Op259Transport
/-! PREPARED: names and carriers must be checked against fresh extraction. -/
set_option autoImplicit false
namespace R1Z.PV_CB_Op259Transport
open ProverRwFull
abbrev Row := aspis_core.r0_transcript.CircleRow
abbrev RawRow := PV_CB_ShippedOp259.aspis_core.r0_transcript.CircleRow
abbrev Point := aspis_core.circle.SecureCirclePoint
abbrev RawPoint := PV_CB_ShippedOp259.aspis_core.circle.SecureCirclePoint

def encodeRow : Row → RawRow
  | .First => .First
  | .Second => .Second
def decodeRow : RawRow → Row
  | .First => .First
  | .Second => .Second
def encodePoint (x : Point) : RawPoint := ⟨encode x.x, encode x.y⟩
def decodePoint (x : RawPoint) : Point := ⟨decode x.x, decode x.y⟩

theorem native_row_roundtrip (x : Row) : decodeRow (encodeRow x) = x := by
  cases x <;> rfl
theorem extracted_row_roundtrip (x : RawRow) : encodeRow (decodeRow x) = x := by
  cases x <;> rfl
theorem native_point_roundtrip (x : Point) : decodePoint (encodePoint x) = x := by
  cases x
  simp only [decodePoint, encodePoint, native_roundtrip]
theorem extracted_point_roundtrip (x : RawPoint) : encodePoint (decodePoint x) = x := by
  cases x
  simp only [encodePoint, decodePoint, extracted_roundtrip]

#print axioms native_row_roundtrip
#print axioms extracted_row_roundtrip
#print axioms native_point_roundtrip
#print axioms extracted_point_roundtrip
end R1Z.PV_CB_Op259Transport
