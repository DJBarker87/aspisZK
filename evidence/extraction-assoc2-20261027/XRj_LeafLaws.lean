import XRh_Release.FunsExternal
open Aeneas Aeneas.Std Result XRh_Release
namespace XRj_LeafLaws
/- These laws concern the DEFINED release-namespace reference externals.
   Their P6 shipped == reference bridges remain open. No whole-top credit. -/
theorem checkValues_short (bytes : Slice U8) (h : bytes.val.length < 16) :
    compact.check_values bytes = ok (.Ok ()) := by
  simp [compact.check_values, XRj_Bytes.chunksValid, Nat.div_eq_of_lt h]

theorem echeck_short (bytes : Slice U8) (k : Bool) (h : bytes.val.length < 32) :
    verifier.echeck bytes k = ok (.Ok ()) := by
  simp [verifier.echeck, XRj_Bytes.chunksValid, Nat.div_eq_of_lt h]

theorem validate_short (row : U8) (bytes : Slice U8) (h : bytes.val.length < 32) :
    r1_wire.validate_record_fields row bytes = ok (.Ok ()) := by
  simp [r1_wire.validate_record_fields, Nat.div_eq_of_lt h]

theorem expand_alignment_frame (bytes out : Slice U8)
    (h : bytes.val.length % 16 ≠ 0) :
    compact.expand_values bytes out = ok (.Err .Length, out) := by
  simp [compact.expand_values, h]

theorem q_roundtrip (q : aspis_core.field.QM31) :
    XRj_FieldExternal.newQ (XRj_FieldExternal.oldQ q) = q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

theorem q_old_roundtrip (q : AspisR1PublicPreparation.aspis_core.field.QM31) :
    XRj_FieldExternal.oldQ (XRj_FieldExternal.newQ q) = q := by
  cases q with | mk c0 c1 => cases c0; cases c1; rfl

/-- A concrete non-vacuity witness for these external leaf models only. -/
theorem leaf_nonvacuity : ∃ bytes : Slice U8,
    compact.check_values bytes = ok (.Ok ()) ∧
    verifier.echeck bytes true = ok (.Ok ()) ∧
    r1_wire.validate_record_fields 0#u8 bytes = ok (.Ok ()) := by
  let bytes : Slice U8 := ⟨[], by simp⟩
  exact ⟨bytes, checkValues_short bytes (by decide),
    echeck_short bytes true (by decide), validate_short 0#u8 bytes (by decide)⟩

#print axioms checkValues_short
#print axioms echeck_short
#print axioms validate_short
#print axioms expand_alignment_frame
#print axioms q_roundtrip
#print axioms q_old_roundtrip
#print axioms leaf_nonvacuity
end XRj_LeafLaws
