import R1Z.PV_CB_Op71Funs
set_option autoImplicit false
namespace PV_L2C_CanonicalParser
open Aeneas Aeneas.Std Result PV_CB_ShippedOp71
/-- The real scalar byte primitives, rather than a codec-success premise. -/
theorem word_roundtrip (x : U32) :
    core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  cases x
  simp [core.num.U32.from_le_bytes,core.num.U32.to_le_bytes,
    List.map_map,Function.comp_def,BitVec.fromLEBytes,BitVec.toLEBytes]
#print axioms word_roundtrip

/-- The actual extracted native >=P branch takes its accepting arm. -/
theorem scalar_parse (x : U32) (hx : x.val<2147483647) :
    aspis_core.field.M31.from_le_bytes (core.num.U32.to_le_bytes x)=ok (some x) := by
  have h : ¬ x≥aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  unfold aspis_core.field.M31.from_le_bytes
  rw [word_roundtrip]
  change (if x≥aspis_core.field.P then ok none else ok (some x))=ok (some x)
  rw [if_neg h]
#print axioms scalar_parse
end PV_L2C_CanonicalParser
